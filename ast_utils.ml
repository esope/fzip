open Ast
open Location

let string_of_token = Lexer.string_of_token

module Encode = struct
  open Ast

  module Typ = struct
    open Typ

    let rec kind_rec typ = function
      | Raw.Base -> Base
      | Raw.Pi(x, k1, k2) ->
          let k1' = kind_rec typ k1
          and k2' = kind_rec typ k2 in
          mkPi (Var.make x) k1' k2'
      | Raw.Sigma f ->
          let f = Label.AList.map
              (fun (x, k) -> (Var.make x, kind_rec typ k)) f in
          mkSigma f
      | Raw.Single t -> Single (typ t)

    let rec typ_rec kind t =
      { t with content = pre_typ_rec kind t.content }
    and pre_typ_rec kind = function
      | Raw.Var x -> FVar (Var.make x)
      | Raw.App (t, u) -> App (typ_rec kind t, typ_rec kind u)
      | Raw.Lam (x, k, t) ->
          let k' = { k with content = kind k.content }
          and t' = typ_rec kind t in
          mkLam (Var.make x) k' t'
      | Raw.Record m -> Record (Label.Map.map (typ_rec kind) m)
      | Raw.Proj (t, lab) -> Proj (typ_rec kind t, lab)
      | Raw.BaseForall (x, k, t) ->
          let k' = { k with content = kind k.content }
          and t' = typ_rec kind t in
          mkBaseForall (Var.make x) k' t'
      | Raw.BaseRecord m -> BaseRecord (Label.Map.map (typ_rec kind) m)
      | Raw.BaseArrow (t, u) -> BaseArrow (typ_rec kind t, typ_rec kind u)

(* closing recursion *)
    let rec typ t = typ_rec kind t
    and kind k = kind_rec typ k
        
  end

  module Term = struct
    open Ast.Term

    let rec term t =
      { t with content = pre_term t.content }
    and pre_term = function
      | Raw.TeVar x -> FVar (Var.make x)
      | Raw.TeApp (t, u) -> App (term t, term u)
      | Raw.TeLam (x, tau, t) ->
          let tau' = Typ.typ tau
          and t' = term t in
          mkLam (Var.make x)tau' t'
      | Raw.TeRecord m -> Record (Label.AList.map term m)
      | Raw.TeProj (t, lab) -> Proj (term t, lab)
      | Raw.TeGen (x, k, t) ->
          let k' = { k with content = Typ.kind k.content }
          and t' = term t in
          mkGen (Ast.Typ.Var.make x) k' t'
      | Raw.TeInst (t, tau) -> Inst(term t, Typ.typ tau)
  end
end

module Decode = struct
  open Ast

  module Typ = struct
    open Raw

    let rec kind_rec typ = function
      | Typ.Base -> Base
      | Typ.Pi(x, k1, k2) ->
          let k1' = kind_rec typ k1
          and k2' = kind_rec typ k2 in
          Pi(Typ.Var.bto_string x, k1', k2')
      | Typ.Sigma f ->
          Sigma (Label.AList.map
                   (fun (x,k) -> (Typ.Var.bto_string x, kind_rec typ k)) f)
      | Typ.Single t -> Single (typ t)

    let rec typ_rec kind t =
      { t with content = pre_typ_rec kind t.content }
    and pre_typ_rec kind = function
      | Typ.FVar x -> Var (Typ.Var.to_string x)
      | Typ.BVar x -> Var (Typ.Var.bto_string x)
      | Typ.App (t, u) -> App (typ_rec kind t, typ_rec kind u)
      | Typ.Lam (x, k, t) ->
          let k' = { k with content = kind k.content }
          and t' = typ_rec kind t in
          Lam(Typ.Var.bto_string x, k', t')
      | Typ.Record m -> Record (Label.Map.map (typ_rec kind) m)
      | Typ.Proj (t, lab) -> Proj (typ_rec kind t, lab)
      | Typ.BaseForall (x, k, t) ->
          let k' = { k with content = kind k.content }
          and t' = typ_rec kind t in
          BaseForall(Typ.Var.bto_string x, k', t')
      | Typ.BaseRecord m -> BaseRecord (Label.Map.map (typ_rec kind) m)
      | Typ.BaseArrow (t, u) -> BaseArrow (typ_rec kind t, typ_rec kind u)

(* closing recursion *)
    let rec typ t = typ_rec kind t
    and kind k = kind_rec typ k

  end

end

module PPrint = struct
  open Ast.Raw
  type doc = Pprint.document

  let is_delimited = function
    | Pi(_,_,_) -> false
    | Base | Sigma _ | Single _ -> true

  let ident = Pprint.text

  let rec kind_rec typ = let open Pprint in function
    | Base -> text "⋆"
    | Pi(x, k1, k2) ->
        prefix "Π"
          ((parens (infix_com "::" (ident x) (kind_rec typ k1))) ^^
           break1 ^^
           (kind_rec typ k2))
    | Sigma f ->
        seq2 "<" " " ">"
          (Label.AList.fold
             (fun lab (x, k) acc ->
               (prefix "type"
                  (prefix lab
                     (prefix "as"
                        (infix "::" (ident x)
                           (kind_rec typ k)))))
               :: acc)
             f [])
    | Single t ->
        prefix "S"
          (parens (typ t))

  let is_delimited t =
    match t.content with
    | Lam(_,_,_) -> false
    | Var _ | Record _ | Proj(_,_) | App(_,_) |
      BaseArrow (_, _) | BaseRecord _ | BaseForall (_, _, _)-> true
  let is_app t = match t.content with
  | App(_,_) -> true
  | Var _ | BaseArrow (_, _) | BaseRecord _ | BaseForall (_, _, _) |
    Proj (_, _) | Record _ | Lam (_, _, _)-> false
  let is_proj t = match t.content with
  | Proj(_,_) -> true
  | Var _ | BaseArrow (_, _) | BaseRecord _ | BaseForall (_, _, _) |
    Record _ | Lam (_, _, _) | App (_, _)-> false
  let is_base_arrow t = match t.content with
  | BaseArrow(_,_) -> true
  | Var _ | BaseRecord _ | BaseForall (_, _, _) | Proj (_, _) |
    Record _ | Lam (_, _, _) | App (_, _)-> false
  let is_base_record t = match t.content with
  | BaseRecord _ -> true
  | Var _ | BaseArrow (_, _) | BaseForall (_, _, _) | Proj (_, _) |
    Record _ | Lam (_, _, _) | App (_, _) -> false
  let tights_more_than_app x =
    match x.content with
    | Var _ | Record _ | Proj _ | BaseRecord _ -> true
    | BaseArrow (_, _) | BaseForall (_, _, _) |
      Lam (_, _, _) | App(_,_) -> false
  let tights_more_than_record x =
    match x.content with
    | Var _ | Record _ | Proj _ | BaseRecord _ -> true
    | BaseArrow (_, _) | BaseForall (_, _, _) |
      Lam (_, _, _) | App(_,_) -> false
  let tights_more_than_proj x =
    match x.content with
    | Var _ | Record _ | Proj _ | BaseRecord _ -> true
    | BaseArrow (_, _) | BaseForall (_, _, _) |
      Lam (_, _, _) | App(_,_) -> false
  let tights_more_than_base_record x =
    match x.content with
    | Var _ | Record _ | Proj _ | BaseRecord _ -> true
    | BaseArrow (_, _) | BaseForall (_, _, _) |
      Lam (_, _, _) | App(_,_) -> false
  let tights_more_than_base_arrow x =
    match x.content with
    | Var _ | Record _ | Proj _ | BaseRecord _
    | BaseArrow(_,_) -> true
    | BaseForall (_, _, _) | Lam (_, _, _) | App(_,_) -> false


  let rec pre_typ_rec kind = let open Pprint in function
    | Var x -> ident x
    | Lam(x, k, t) ->
        text "λ" ^^
        infix_com ""
          (parens (infix_com "::" (ident x) (kind k.content)))
          (typ_rec kind t)
    | App(t1, t2) ->
        infix_dot " "
          (if (tights_more_than_app t1 && is_delimited t1) || is_app t1
          then typ_rec kind t1
          else parens (typ_rec kind t1))
          (if tights_more_than_app t2 && is_delimited t2
          then typ_rec kind t2
          else parens (typ_rec kind t2))
    | Record m ->
        seq2 "<" " " ">"
          (Label.Map.fold
             (fun lab ty acc ->
               (prefix "type" (prefix lab (prefix "=" (typ_rec kind ty))))
               :: acc)
             m [])
    | Proj(t, lab) ->
        infix_dot "."
          (if is_proj t || (tights_more_than_proj t && is_delimited t)
          then typ_rec kind t
          else parens (typ_rec kind t))
          (text lab.content)
    | BaseArrow(t1,t2) ->
        infix "→"
          (if is_delimited t1 && tights_more_than_base_arrow t1
          then typ_rec kind t1
          else parens (typ_rec kind t1))
          (if is_base_arrow t2
         || (is_delimited t2 && tights_more_than_base_arrow t2)
          then typ_rec kind t2
          else parens (typ_rec kind t2))
    | BaseRecord m ->
        seq2 "{" " " "}"
          (Label.Map.fold
             (fun lab ty acc ->
               (prefix "val" (prefix lab (prefix ":" (typ_rec kind ty))))
               :: acc)
             m [])
    | BaseForall(x, k, t) ->
        text "∀" ^^
        infix_com ""
          (parens (infix_com "::" (ident x) (kind k.content)))
          (typ_rec kind t)
  and typ_rec kind { content ; _ } = Pprint.group1 (pre_typ_rec kind content)

  let rec typ t = typ_rec kind t
  and kind k = kind_rec typ k

  let string_from_buffer buffer t =
    let buff = Buffer.create 80 in
    let () = buffer buff t in
    Buffer.contents buff

  module Typ = struct
    module Raw = struct
      let channel chan t = Pprint.Channel.pretty 100.0 80 chan (typ t)
      let buffer buff t = Pprint.Buffer.pretty 100.0 80 buff (typ t)
      let string = string_from_buffer buffer
    end
    let channel chan t = Raw.channel chan (Decode.Typ.typ t)
    let buffer buff t = Raw.buffer buff (Decode.Typ.typ t)
    let string t = Raw.string (Decode.Typ.typ t)
  end

  module Kind = struct
    module Raw = struct
      let channel chan k = Pprint.Channel.pretty 100.0 80 chan (kind k)
      let buffer buff k = Pprint.Buffer.pretty 100.0 80 buff (kind k)
      let string = string_from_buffer buffer
    end
    let channel chan k = Raw.channel chan (Decode.Typ.kind k)
    let buffer buff k = Raw.buffer buff (Decode.Typ.kind k)
    let string k = Raw.string (Decode.Typ.kind k)
  end

end
