open Ast
open Term
open Wftype
open Location
open Ast_utils

type env = (Typ.typ, Typ.typ Typ.kind) Env.t

type basekind_res = OK | KIND of Typ.typ Typ.kind
let wfbasetype env t =
  let k = wftype env t in
  if wfsubkind_b env k Typ.Base
  then OK
  else KIND k

let rec wfterm env t = dummy_locate (pre_wfterm env t.content)
and pre_wfterm env = function
  | BVar _ -> assert false
  | FVar x -> (Env.get_term_var x env).content
  | Lam (x, t, e) ->
      begin
        match wfbasetype env t with
        | OK ->
            let x' = Var.bfresh x in
            let x_var' = dummy_locate (FVar x') in
            let t' =
              wfterm (Env.add_term_var x' t env) (bsubst_term_var e x x_var') in
            Typ.BaseArrow(t, t')
        | KIND k ->
            Error.raise_error Error.term_wf t.startpos t.endpos
              (Printf.sprintf "This type should have kind ⋆, but has kind\n%s%!"
                 (PPrint.Kind.string k))
      end
  | App(e1, e2) ->
      begin
        match (wfterm env e1).content with
        | Typ.BaseArrow(tau2', tau1') ->
            begin
              let tau2 = wfterm env e2 in
              let open Answer in
              match wfsubtype env tau2 tau2' with
              | Yes -> tau1'.content
              | No reason ->
                  Error.raise_error Error.subtype e1.startpos e2.endpos
                    (Printf.sprintf "Ill-formed application\n%s%!"
                       (error_msg reason))
            end
        | tau ->
            Error.raise_error Error.term_wf e1.startpos e2.startpos
              (Printf.sprintf
                 "Non functional application: this term should have an arrow type,\nbut has type\n%s%!"
                 (PPrint.Typ.string (dummy_locate tau)))
      end
  | Gen (x, k, e) ->
      if wfkind env k.content
      then
        let x' = Typ.Var.bfresh x in
        let x_var' = dummy_locate (Typ.FVar x') in
        let t' =
          wfterm (Env.add_typ_var x' k.content env) (bsubst_typ_var e x x_var') in
        Typ.mkBaseForall x' k t'
      else
        Error.raise_error Error.kind_wf k.startpos k.endpos
          "Ill-formed kind at the bound of a generalization."
  | Inst(e, tau) ->
      begin
        match (wfterm env e).content with
        | Typ.BaseForall(x, k', tau') ->
            begin
              let k = wftype env tau in
              let open Answer in
              match wfsubkind env k k'.content with
              | Yes -> (Typ.bsubst_typ tau' x tau).content
              | No reasons ->
                  Error.raise_error Error.subkind e.startpos tau.endpos
                    (Printf.sprintf "Ill-formed instantiation:\n%s%!"
                       (error_msg reasons))
            end
        | tau' ->
            Error.raise_error Error.term_wf e.startpos e.endpos
              (Printf.sprintf
                 "Ill-formed instantiation: this term should have a universal type,\nbut has type\n%s%!"
                 (PPrint.Typ.string (dummy_locate tau')))
      end
  | Pair(e1, e2) ->
      let t1 = wfterm env e1
      and t2 = wfterm env e2 in
      Typ.BaseProd(t1, t2)
  | Proj(e, lab) ->
      begin
        match (wfterm env e).content with
        | Typ.BaseProd(t1, t2) ->
            if lab.content = "fst" then t1.content
            else if lab.content = "snd" then t2.content
            else
              Error.raise_error Error.term_wf lab.startpos lab.endpos
                ("Unknown label " ^ lab.content ^ ".")
        | tau ->
            Error.raise_error Error.term_wf e.startpos e.endpos
              (Printf.sprintf
                 "Ill-formed projection: this term should have a record type,\nbut has type\n%s%!"
                 (PPrint.Typ.string (dummy_locate tau)))
      end
