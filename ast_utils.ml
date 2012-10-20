open Location

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
      | Raw.TeRecord m ->
          let m = Label.AList.map
              (fun (x, e) ->
                let x = match x with
                | None -> dummy_locate (Var.make (Var.to_string (Var.fresh ())))
                | Some x -> locate_with (Var.make x.content) x
                in (x, term e)) m in
          mkRecord m
      | Raw.TeProj (t, lab) -> mkProj (term t) lab
      | Raw.TeGen (x, k, t) ->
          let k' = { k with content = Typ.kind k.content }
          and t' = term t in
          mkGen (map Ast.Typ.Var.make x) k' t'
      | Raw.TeInst (t, tau) -> mkInst (term t) (Typ.typ tau)
      | Raw.TeFix (x, tau, t) ->
          let tau' = Typ.typ tau
          and t' = term t in
          mkFix (map Var.make x) tau' t'
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

    let rec kind_rec best typ = function
      | Typ.Base -> Base
      | Typ.Pi(x, k1, k2) ->
          let k1' = kind_rec best typ k1 in
          if Kind.bvar_occurs x k2
          then
            let (best, x') = Typ.Var.Best.remember_get best x in
            let k2' = kind_rec best typ k2 in
            Pi(Some (Typ.Var.to_string x'), k1', k2')
          else
            let k2' = kind_rec best typ k2 in
            Pi(None, k1', k2')
      | Typ.Sigma f -> Sigma (kind_rec_fields best typ f)
      | Typ.Single (t, k) -> Single (typ best t, kind_rec best typ k)

    and kind_rec_fields best typ = function
      | [] -> []
      | (lab, (x, k)) :: f ->
        let k' = kind_rec best typ k in
        if Kind.bvar_occurs_fields x f
        then
          let (best, x') = Typ.Var.Best.remember_get best x in
          (lab, (Some (Typ.Var.to_string x'), k')) :: kind_rec_fields best typ f
        else
          (lab, (None, k')) :: kind_rec_fields best typ f

    let rec typ_rec best kind t =
      { t with content = pre_typ_rec best kind t.content }
    and pre_typ_rec best kind = function
      | Typ.FVar x -> Var (Typ.Var.to_string x)
      | Typ.BVar x -> Var (Typ.Var.to_string (Typ.Var.Best.get best x))
      | Typ.App (t, u) -> App (typ_rec best kind t, typ_rec best kind u)
      | Typ.Lam (x, k, t) ->
          let k' = { k with content = kind best k.content } in
          let (best, x') = Typ.Var.Best.remember_get best x.content in
          let t' = typ_rec best kind t in
          Lam(locate_with (Typ.Var.to_string x') x, k', t')
      | Typ.Record m -> Record (Label.Map.map (typ_rec best kind) m)
      | Typ.Proj (t, lab) -> Proj (typ_rec best kind t, lab)
      | Typ.BaseForall (x, k, t) ->
          let k' = { k with content = kind best k.content } in
          let (best, x') = Typ.Var.Best.remember_get best x.content in
          let t' = typ_rec best kind t in
          BaseForall(locate_with (Typ.Var.to_string x') x, k', t')
      | Typ.BaseExists (x, k, t) ->
          let k' = { k with content = kind best k.content } in
          let (best, x') = Typ.Var.Best.remember_get best x.content in
          let t' = typ_rec best kind t in
          BaseExists(locate_with (Typ.Var.to_string x') x, k', t')
      | Typ.BaseRecord m ->
          BaseRecord (Label.Map.map (typ_rec best kind) m)
      | Typ.BaseArrow (t, u) ->
          BaseArrow (typ_rec best kind t, typ_rec best kind u)

(* closing recursion *)
    let rec typ best t = typ_rec best kind t
    and kind best k = kind_rec best typ k

(* initialization *)
    let typ  = typ  Typ.Var.Best.empty
    let kind = kind Typ.Var.Best.empty

  end

end

module PPrint = struct
  open Ast.Raw
  type doc = Pprint.document

  let ident = Pprint.text

  let sequence s d e l = let open Pprint in match l with
    | [] -> text s ^^ text e
    | _ ->
      soft_surround 1 break1 (text s) (group (sepmap d (fun x -> x) l)) (text e)


  type kind_level =
  | Simple_kind
  | Arrow_kind
  | Kind

  let rec kind_rec level typ = let open Pprint in match level with
    | Simple_kind -> begin function
      | Base -> text "⋆"
      | Sigma f ->
        sequence "<" (break 1) ">"
          (List.map
             (fun (lab, (x, k)) ->
               group
                 (infix "::"
                    (string "type " ^^ string lab ^^
                       (match x with
                       | Some x -> string " as " ^^ ident x
                       | None -> empty))
                    (kind_rec Kind typ k)))
             f)
      | Single (t, Base) ->
        prefix "S" (parens (typ t))
      | Single (t, k) ->
        prefix "S" (parens (infix "::" (typ t) (kind_rec Kind typ k)))
      | (Pi _) as k -> parens (kind_rec Kind typ k)
    end
    | Arrow_kind -> begin function
      | Pi(None, k1, k2) ->
        infix "⇒"
          (kind_rec Simple_kind typ k1)
          (kind_rec Arrow_kind  typ k2)
      | (Base | Sigma _ | Single _ | Pi (Some _, _, _)) as k ->
        kind_rec Simple_kind typ k
    end
    | Kind -> begin function
      | Pi(Some x, k1, k2) ->
        infix "⇒"
          (prefix "Π"
             (parens (infix "::" (ident x) (kind_rec Kind typ k1))))
          (kind_rec Kind typ k2)
      | (Base | Sigma _ | Single _ | Pi (None, _, _)) as k ->
        kind_rec Arrow_kind typ k
    end

  type typ_level =
  | Simple_typ
  | App_typ
  | Arrow_typ
  | Typ

  let rec pre_typ_rec level kind = let open Pprint in match level with
    | Simple_typ -> begin function
      | Var x -> ident x
      | Record m ->
        sequence "<" (break 1) ">"
          (List.map
             (fun (lab, ty) ->
               group
                 (infix "="
                    (string "type " ^^ string lab)
                    (typ_rec Typ kind ty)))
             (Label.Map.bindings m))
      | Proj(t, lab) ->
        infix_dot "."
          (typ_rec Simple_typ kind t)
          (text lab.content)
      | BaseRecord m ->
        sequence "{" (break 1) "}"
          (List.map
             (fun (lab, ty) ->
               group
                 (infix ":"
                    (string "val " ^^ string lab)
                    (typ_rec Typ kind ty)))
             (Label.Map.bindings m))
      | (App _ | BaseArrow _ | Lam _ | BaseForall _ | BaseExists _) as t ->
        parens (pre_typ_rec Typ kind t)
    end
    | App_typ -> begin function
      | App(t1, t2) ->
        (typ_rec App_typ kind t1)
        ^^ break1
        ^^ (typ_rec Simple_typ kind t2)
      | (Var _ | Record _ | Proj _ | BaseRecord _ | BaseArrow _ | Lam _ |
          BaseForall _ | BaseExists _) as t ->
        pre_typ_rec Simple_typ kind t
    end
    | Arrow_typ -> begin function
      | BaseArrow(t1,t2) ->
        infix "→"
          (typ_rec App_typ kind t1)
          (typ_rec Typ kind t2)
      | (Var _ | Record _ | Proj _ | BaseRecord _ | App _ | Lam _ |
          BaseForall _ | BaseExists _) as t ->
        pre_typ_rec App_typ kind t
    end
    | Typ -> begin function
      | Lam({ content = x ; _ }, k, t) ->
        infix_com "⇒"
        (text "λ" ^^ blank 1 ^^
           (parens (infix "::" (ident x) (kind k.content))))
        (typ_rec Typ kind t)
      | BaseForall({ content = x ; _ }, k, t) ->
        infix_com ","
        (text "∀" ^^ blank 1 ^^
           (parens (infix "::" (ident x) (kind k.content))))
        (typ_rec Typ kind t)
      | BaseExists({ content = x ; _ }, k, t) ->
        infix_com ","
        (text "∃" ^^ blank 1 ^^
           (parens (infix "::" (ident x) (kind k.content))))
        (typ_rec Typ kind t)
      | (Var _ | Record _ | Proj _ | BaseRecord _ | App _ | BaseArrow _) as t ->
        pre_typ_rec Arrow_typ kind t
    end

  and typ_rec level kind { content ; _ } = Pprint.group1 (pre_typ_rec level kind content)

  let rec typ t = typ_rec Typ kind t
  and kind k = kind_rec Kind typ k

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
