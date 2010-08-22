open Ast
open Location

let string_of_token = Lambda_lexer.string_of_token

module Encode = struct
  open Ast.Raw

  let rec kind_rec typ = function
    | RBase -> Base
    | RArrow(k1, k2) ->
        Arrow(kind_rec typ k1, kind_rec typ k2)
    | RProd(k1, k2) ->
        Prod(kind_rec typ k1, kind_rec typ k2)
    | RPi(x, k1, k2) ->
        let k1' = kind_rec typ k1
        and k2' = kind_rec typ k2 in
        mkPi x k1' k2'
    | RSigma(x, k1, k2) ->
        let k1' = kind_rec typ k1
        and k2' = kind_rec typ k2 in
        mkSigma x k1' k2'
    | RSingle t -> Single (typ t)

  let rec typ_rec kind t =
    { t with content = pre_typ_rec kind t.content }
  and pre_typ_rec kind = function
    | RVar x -> FVar x
    | RApp (t, u) -> App (typ_rec kind t, typ_rec kind u)
    | RLam (x, k, t) ->
        let k' = kind k
        and t' = typ_rec kind t in
        mkLam x k' t'
    | RPair (t, u) -> Pair (typ_rec kind t, typ_rec kind u)
    | RProj (t, lab) -> Proj (typ_rec kind t, lab)

(* closing recursion *)
  let rec typ t = typ_rec kind t
  and kind k = kind_rec typ k

end

module Gen = struct
  let () = Random.self_init ()
  let letter () = Char.escaped (Char.chr (Random.int 10))

  open Ast.Raw

  let rec typ n =
    Location.locate (pre_typ n) Lexing.dummy_pos Lexing.dummy_pos
  and pre_typ = function
    | 0 -> RVar (letter ())
    | 1 -> RLam (letter (), RBase, typ 0)
    | n ->
        if Random.float 1. < 0.9
        then RLam (letter (), RBase, typ (n-1))
        else begin match Random.int 3 with
        | 0 -> RProj(typ (n-1), "1")
        | 1 -> let m = Random.int n in
          RApp(typ m, typ (n - 1 - m))
        | 2 -> let m = Random.int n in
          RPair(typ m, typ (n - 1 - m))
        | _ -> assert false
        end
end

module Measure = struct

  let rec size { content = content ; startpos = _ ; endpos = _ } =
    pre_size content
  and pre_size = function
    | FVar _ | BVar _ -> 1
    | App(t1, t2) | Pair(t1, t2) -> 1 + size t1 + size t2
    | Lam(_, _, t) | Proj(t, _) -> 1 + size t

  let rec nb_binders { content = content ; startpos = _ ; endpos = _ } =
    pre_nb_binders content
  and pre_nb_binders = function
    | FVar _ | BVar _ -> 0
    | App(t1, t2) | Pair(t1, t2) -> nb_binders t1 + nb_binders t2
    | Proj(t, _) -> nb_binders t
    | Lam(_, _, t) -> 1 + nb_binders t

  let rec height { content = content ; startpos = _ ; endpos = _ } =
    pre_height content
  and pre_height = function
    | FVar _ | BVar _ -> 1
    | App(t1, t2) | Pair(t1, t2) -> 1 + max (height t1) (height t2)
    | Lam(_, _, t) | Proj(t, _) -> 1 + height t

  let rec bheight { content = content ; startpos = _ ; endpos = _ } =
    pre_bheight content
  and pre_bheight = function
    | FVar _ | BVar _ -> 0
    | App(t1, t2) | Pair(t1, t2) -> max (bheight t1) (bheight t2)
    | Proj(t, _) -> bheight t
    | Lam(_, _, t) -> 1 + bheight t

end

module String = struct

  let tights_more_than_arrow = function
    | Arrow(_,_) -> false
    | _ -> true
  let tights_more_than_prod = function
    | Prod(_,_) | Arrow(_, _) -> false
    | _ -> true
  let is_arrow = function
    | Arrow(_,_) -> true
    | _ -> false
  let is_prod = function
    | Prod(_,_) -> true
    | _ -> false
  let is_delimited = function
    | Sigma(_,_,_) | Pi(_,_,_) -> false
    | _ -> true

  let rec of_kind_rec term = function
    | Base -> Printf.sprintf "%s" (string_of_token Lambda_parser.STAR)
    | Arrow(t1, t2) ->
        (match (tights_more_than_arrow t1 && is_delimited t1,
                is_arrow t2 || tights_more_than_arrow t2 || is_delimited t2) with
        | true, true   -> Printf.sprintf "%a %s %a"
        | true, false  -> Printf.sprintf "%a %s (%a)"
        | false, true  -> Printf.sprintf "(%a) %s %a"
        | false, false -> Printf.sprintf "(%a) %s (%a)")
          (fun _ -> of_kind_rec term) t1
          (string_of_token Lambda_parser.DBLARROW)
          (fun _ -> of_kind_rec term) t2
    | Prod(t1, t2) ->
        (match (tights_more_than_prod t1 && is_delimited t1,
                is_prod t2 || tights_more_than_prod t2 || is_delimited t2) with
        | true, true   -> Printf.sprintf "%a %s %a"
        | true, false  -> Printf.sprintf "%a %s (%a)"
        | false, true  -> Printf.sprintf "(%a) %s %a"
        | false, false -> Printf.sprintf "(%a) %s (%a)")
          (fun _ -> of_kind_rec term) t1
          (string_of_token Lambda_parser.TIMES)
          (fun _ -> of_kind_rec term) t2
    | Pi(x, t1, t2) ->
        Printf.sprintf "%s(%i%s %a) %a"
          (string_of_token Lambda_parser.PI)
          x
          (string_of_token Lambda_parser.DBLCOLON)
          (fun _ -> of_kind_rec term) t1
          (fun _ -> of_kind_rec term) t2
    | Sigma(x, t1, t2) ->
        Printf.sprintf "%s(%i%s %a) %a"
          (string_of_token Lambda_parser.SIGMA)
          x
          (string_of_token Lambda_parser.DBLCOLON)
          (fun _ -> of_kind_rec term) t1
          (fun _ -> of_kind_rec term) t2
    | Single t ->
        Printf.sprintf "%s(%a)"
          (string_of_token Lambda_parser.SINGLE)
          (fun _ -> term) t

  let is_delimited t =
    match t.content with
    | Lam(_,_,_) -> false
    | _ -> true
  let tights_more_than_app x =
    match x.content with
    | BVar _ | FVar _ | Pair(_, _) | Proj _ -> true
    | _ -> false
  let tights_more_than_pair x =
    match x.content with
    | BVar _ | FVar _ | Pair (_,_) | Proj _ -> true
    | _ -> false
  let tights_more_than_proj x =
    match x.content with
    | BVar _ | FVar _ | Pair(_, _) | Proj _ -> true
    | _ -> false

  let rec pre_of_typ = function
    | FVar x -> Printf.sprintf "%s" (string_of_token (Lambda_parser.ID x))
    | BVar x -> Printf.sprintf "%i" x
    | App (t, u) ->
        (match (tights_more_than_app t && is_delimited t,
                tights_more_than_app u && is_delimited u) with
        | true, true -> Printf.sprintf "%a %s%a"
        | true, false -> Printf.sprintf "%a %s(%a)"
        | false, true -> Printf.sprintf "(%a) %s%a"
        | false, false -> Printf.sprintf "(%a) %s(%a)")
          (fun _ -> of_typ) t
          (string_of_token Lambda_parser.APP)
          (fun _ -> of_typ) u
    | Lam (x, tau, t) -> Printf.sprintf "%s(%i %s %a) %a"
          (string_of_token Lambda_parser.LAMBDA)
          x
          (string_of_token Lambda_parser.DBLCOLON)
          (fun _ -> of_kind_rec of_typ) tau
          (fun _ -> of_typ) t
    | Pair (t, u) ->
        (match (tights_more_than_pair t && is_delimited t,
                tights_more_than_pair u) with
        | true, true   -> Printf.sprintf "%s%a%s %a%s"
        | true, false  -> Printf.sprintf "%s%a%s (%a)%s"
        | false, true  -> Printf.sprintf "%s(%a)%s %a%s"
        | false, false -> Printf.sprintf "%s(%a)%s (%a)%s")
          (string_of_token Lambda_parser.LANGLE)
          (fun _ -> of_typ) t
          (string_of_token Lambda_parser.COMMA)
          (fun _ -> of_typ) u
          (string_of_token Lambda_parser.RANGLE)
    | Proj(t, lab) ->
        (if tights_more_than_proj t && is_delimited t
        then Printf.sprintf "%a%s%s"
        else Printf.sprintf "(%a)%s%s")
          (fun _ -> of_typ) t
          (string_of_token Lambda_parser.DOT)
          lab
  and of_typ t = pre_of_typ t.content
  let of_kind = of_kind_rec of_typ

end

module Print = struct
  let typ t = Printf.printf "%s" (String.of_typ t)
  let kind k = Printf.printf "%s" (String.of_kind k)
end
