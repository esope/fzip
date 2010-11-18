open Ast
open Location

let string_of_token = Lexer.string_of_token

module Encode = struct
  open Ast

  module Typ = struct
    open Typ

    let rec kind_rec typ = let open Kind in function
      | Raw.Base -> mkBase
      | Raw.Pi(Some x, k1, k2) ->
          let k1' = kind_rec typ k1
          and k2' = kind_rec typ k2 in
          Kind.mkPi (Var.make x) k1' k2'
      | Raw.Pi(None, k1, k2) ->
          let k1' = kind_rec typ k1
          and k2' = kind_rec typ k2 in
          Kind.mkArrow k1' k2'
      | Raw.Sigma f ->
          let f = Label.AList.map
              (fun (x, k) ->
                let x = match x with
                | None -> Var.make (Var.to_string (Var.fresh ()))
                | Some x -> Var.make x
                in (x, kind_rec typ k)) f in
          Kind.mkSigma f
      | Raw.Single (t, k) -> mkSingle (typ t) (kind_rec typ k)

    let rec typ_rec kind t =
      { t with content = pre_typ_rec kind t.content }
    and pre_typ_rec kind = function
      | Raw.Var x -> mkVar (Var.make x)
      | Raw.App (t, u) -> mkApp (typ_rec kind t) (typ_rec kind u)
      | Raw.Lam (x, k, t) ->
          let k' = { k with content = kind k.content }
          and t' = typ_rec kind t in
          mkLam (map Var.make x) k' t'
      | Raw.Record m -> mkRecord (Label.Map.map (typ_rec kind) m)
      | Raw.Proj (t, lab) -> mkProj (typ_rec kind t) lab
      | Raw.BaseForall (x, k, t) ->
          let k' = { k with content = kind k.content }
          and t' = typ_rec kind t in
          mkBaseForall (map Var.make x) k' t'
      | Raw.BaseExists (x, k, t) ->
          let k' = { k with content = kind k.content }
          and t' = typ_rec kind t in
          mkBaseExists (map Var.make x) k' t'
      | Raw.BaseRecord m -> mkBaseRecord (Label.Map.map (typ_rec kind) m)
      | Raw.BaseArrow (t, u) -> mkBaseArrow (typ_rec kind t) (typ_rec kind u)

(* closing recursion *)
    let rec typ t = typ_rec kind t
    and kind k = kind_rec typ k
        
  end

  module Term = struct
    open Ast.Term

    let rec term t =
      { t with content = pre_term t.content }
    and pre_term = function
      | Raw.TeVar x -> mkVar (Var.make x)
      | Raw.TeApp (t, u) -> mkApp (term t) (term u)
      | Raw.TeLam (x, tau, t) ->
          let tau' = Typ.typ tau
          and t' = term t in
          mkLam (map Var.make x) tau' t'
      | Raw.TeLet (x, t1, t2) ->
          let t1' = term t1
          and t2' = term t2 in
          mkLet (map Var.make x) t1' t2'
      | Raw.TeRecord m -> mkRecord (Label.AList.map term m)
      | Raw.TeProj (t, lab) -> mkProj (term t) lab
      | Raw.TeGen (x, k, t) ->
          let k' = { k with content = Typ.kind k.content }
          and t' = term t in
          mkGen (map Ast.Typ.Var.make x) k' t'
      | Raw.TeInst (t, tau) -> mkInst (term t) (Typ.typ tau)
      | Raw.TeAnnot (t, tau) -> mkAnnot (term t) (Typ.typ tau)
      | Raw.TeSigma (y, z, k, tau, t) ->
          mkSigma (map Ast.Typ.Var.make y)
            (map Ast.Typ.Var.make z)
            { k with content = Typ.kind k.content }
            (Typ.typ tau) (term t)
      | Raw.TeOpen (y, t) ->
          mkOpen (map Ast.Typ.Var.make y) (term t)
      | Raw.TeNu (x, k, t) ->
          let k' = { k with content = Typ.kind k.content }
          and t' = term t in
          mkNu (map Ast.Typ.Var.make x) k' t'
      | Raw.TeEx (x, k, t) ->
          let k' = { k with content = Typ.kind k.content }
          and t' = term t in
          mkEx (map Ast.Typ.Var.make x) k' t'
  end

  module Prog = struct
    open Ast.Prog
    let encode_reqs = List.map
        (function
          | Raw.RequireVal (x, t) ->
              RequireVal (map Ast.Term.Var.make x, Typ.typ t)
          | Raw.RequireTyp (x, k) ->
              RequireTyp (map Ast.Typ.Var.make x, map Typ.kind k)
          | Raw.ExportTyp (x, k) ->
              ExportTyp (map Ast.Typ.Var.make x, map Typ.kind k))

    let prog { Raw.reqs ; code } =
      { reqs = encode_reqs reqs ; code = Term.term code }
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
          if Kind.bvar_occurs x k2
          then Pi(Some (Typ.Var.bto_string x), k1', k2')
          else Pi(None, k1', k2')
      | Typ.Sigma f ->
          Sigma
            (Label.AList.map
               (fun (x,k) ->
                 ((if Kind.bvar_occurs_field x f
                 then Some (Typ.Var.bto_string x)
                 else None),
                   kind_rec typ k)) f)
      | Typ.Single (t, k) -> Single (typ t, kind_rec typ k)

    let rec typ_rec kind t =
      { t with content = pre_typ_rec kind t.content }
    and pre_typ_rec kind = function
      | Typ.FVar x -> Var (Typ.Var.to_string x)
      | Typ.BVar x -> Var (Typ.Var.bto_string x)
      | Typ.App (t, u) -> App (typ_rec kind t, typ_rec kind u)
      | Typ.Lam (x, k, t) ->
          let k' = { k with content = kind k.content }
          and t' = typ_rec kind t in
          Lam(map Typ.Var.bto_string x, k', t')
      | Typ.Record m -> Record (Label.Map.map (typ_rec kind) m)
      | Typ.Proj (t, lab) -> Proj (typ_rec kind t, lab)
      | Typ.BaseForall (x, k, t) ->
          let k' = { k with content = kind k.content }
          and t' = typ_rec kind t in
          BaseForall(map Typ.Var.bto_string x, k', t')
      | Typ.BaseExists (x, k, t) ->
          let k' = { k with content = kind k.content }
          and t' = typ_rec kind t in
          BaseExists(map Typ.Var.bto_string x, k', t')
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
    | Base | Sigma _ | Single (_,_) -> true

  let is_non_dep_pi = function
    | Pi(None, _, _) -> true
    | Pi(Some _, _, _) | Base | Sigma _ | Single(_,_) -> false

  let ident = Pprint.text

  let rec kind_rec typ = let open Pprint in function
    | Base -> text "⋆"
    | Pi(Some x, k1, k2) ->
        (prefix "Π"
           (parens (infix_com "::" (ident x) (kind_rec typ k1))) ^^ 
         string "⇒") ^^
           break1 ^^
           (kind_rec typ k2)
    | Pi(None, k1, k2) ->
        infix "⇒"
          (if is_delimited k1 && not (is_non_dep_pi k1)
          then kind_rec typ k1
          else parens (kind_rec typ k1))
          (kind_rec typ k2)
    | Sigma f ->
        seq2 "<" " " ">"
          (Label.AList.fold
             (fun lab (x, k) acc -> match x with
             | Some x ->
                 (infix "::"
                    (string "type " ^^ string lab ^^ string " as " ^^ ident x)
                    (kind_rec typ k)) :: acc
             | None ->
                 (infix "::"
                    (string "type " ^^ string lab)
                    (kind_rec typ k)) :: acc)
             f [])
    | Single (t, Base) ->
        prefix "S"
          (parens (typ t))
    | Single (t, k) ->
        prefix "S"
          (parens (infix "::" (typ t) (kind_rec typ k)))

  let is_delimited t =
    match t.content with
    | Lam(_,_,_) | BaseForall (_, _, _) | BaseExists (_, _, _) -> false
    | Var _ | Record _ | Proj(_,_) | App(_,_) |
      BaseArrow (_, _) | BaseRecord _ -> true
  let is_app t = match t.content with
  | App(_,_) -> true
  | Var _ | BaseArrow (_, _) | BaseRecord _ | BaseForall (_, _, _) |
    BaseExists (_,_,_) | Proj (_, _) | Record _ | Lam (_, _, _)-> false
  let is_proj t = match t.content with
  | Proj(_,_) -> true
  | Var _ | BaseArrow (_, _) | BaseRecord _ | BaseForall (_, _, _) |
    BaseExists (_,_,_) | Record _ | Lam (_, _, _) | App (_, _)-> false
  let is_base_arrow t = match t.content with
  | BaseArrow(_,_) -> true
  | Var _ | BaseRecord _ | BaseForall (_, _, _) | Proj (_, _) |
    BaseExists (_,_,_) | Record _ | Lam (_, _, _) | App (_, _)-> false
  let is_base_record t = match t.content with
  | BaseRecord _ -> true
  | Var _ | BaseArrow (_, _) | BaseForall (_, _, _) | Proj (_, _) |
    BaseExists (_,_,_) | Record _ | Lam (_, _, _) | App (_, _) -> false
  let tights_more_than_app x =
    match x.content with
    | Var _ | Record _ | Proj _ | BaseRecord _ -> true
    | BaseArrow (_, _) | BaseForall (_, _, _) | BaseExists (_,_,_) |
      Lam (_, _, _) | App(_,_) -> false
  let tights_more_than_record x =
    match x.content with
    | Var _ | Record _ | Proj _ | BaseRecord _ -> true
    | BaseArrow (_, _) | BaseForall (_, _, _) | BaseExists (_,_,_) |
      Lam (_, _, _) | App(_,_) -> false
  let tights_more_than_proj x =
    match x.content with
    | Var _ | Record _ | Proj _ | BaseRecord _ -> true
    | BaseArrow (_, _) | BaseForall (_, _, _) | BaseExists (_,_,_) |
      Lam (_, _, _) | App(_,_) -> false
  let tights_more_than_base_record x =
    match x.content with
    | Var _ | Record _ | Proj _ | BaseRecord _ -> true
    | BaseArrow (_, _) | BaseForall (_, _, _) | BaseExists (_,_,_) |
      Lam (_, _, _) | App(_,_) -> false
  let tights_more_than_base_arrow x =
    match x.content with
    | Var _ | Record _ | Proj _ | BaseRecord _
    | BaseArrow(_,_) -> true
    | BaseForall (_, _, _) | BaseExists (_,_,_) |
      Lam (_, _, _) | App(_,_) -> false


  let rec pre_typ_rec kind = let open Pprint in function
    | Var x -> ident x
    | Lam({ content = x ; _ }, k, t) ->
        (prefix "λ"
           (parens (infix "::" (ident x) (kind k.content))) ^^ string "⇒") ^^
        break1 ^^
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
               (infix "="
                  (string "type " ^^ string lab)
                  (typ_rec kind ty))
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
               (infix ":"
                  (string "val " ^^ string lab)
                  (typ_rec kind ty))
               :: acc)
             m [])
    | BaseForall({ content = x ; _ }, k, t) ->
        (prefix "∀"
           (parens (infix_com "::" (ident x) (kind k.content))) ^^
         string ",") ^^
        break1 ^^
        (typ_rec kind t)
    | BaseExists({ content = x ; _ }, k, t) ->
        (prefix "∃"
           (parens (infix_com "::" (ident x) (kind k.content))) ^^
         string ",") ^^
        break1 ^^
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
