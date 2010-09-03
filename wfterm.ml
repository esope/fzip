open Ast
open Term
open Wftype
open Location

type env = (Typ.typ, Typ.typ Typ.kind) Env.t

let dummy_locate = dummy_locate
let wfsubkind = Wftype.wfsubkind
let wfbasetype env t =
  wfsubkind env (wftype env t) Typ.Base

let rec wfterm env t = dummy_locate (pre_wfterm env t.content)
and pre_wfterm env = function
  | BVar _ -> assert false
  | FVar x -> (Env.get_term_var x env).content
  | Lam (x, t, e) ->
      if wfbasetype env t
      then
        let x' = new_var () in
        let x_var' = dummy_locate (FVar x') in
        let t' =
          wfterm (Env.add_term_var x' t env) (bsubst_term_var e x x_var') in
        Typ.BaseArrow(t, t')
      else
        failwith "Ill-formed kind at the bound of a λ."
  | App(e1, e2) ->
      begin
        match (wfterm env e1).content with
        | Typ.BaseArrow(tau2', tau1') ->
            let tau2 = wfterm env e2 in
            if wfsubtype env tau2 tau2'
            then tau1'.content
            else failwith "Ill-formed application (subtyping error)."
        | _ ->
            failwith "Non functional application."
      end
  | Gen (x, k, e) ->
      if wfkind env k
      then
        let x' = Typ.new_var () in
        let x_var' = dummy_locate (Typ.FVar x') in
        let t' =
          wfterm (Env.add_typ_var x' k env) (bsubst_typ_var e x x_var') in
        Typ.mkBaseForall x' k t'
      else
        failwith "Ill-formed kind at the bound of a generalization."
  | Inst(e, tau) ->
      begin
        match (wfterm env e).content with
        | Typ.BaseForall(x, k', tau') ->
            let k = wftype env tau in
            if wfsubkind env k k'
            then (Typ.bsubst_typ tau' x tau).content
            else failwith "Ill-formed instantiation (subkinding error)."
        | _ ->
            failwith "Non universal instantiation."
      end
  | Pair(e1, e2) ->
      let t1 = wfterm env e1
      and t2 = wfterm env e2 in
      Typ.BaseProd(t1, t2)
  | Proj(e, lab) ->
      begin
        match (wfterm env e).content with
        | Typ.BaseProd(t1, t2) ->
            if lab = "fst" then t1.content
            else if lab = "snd" then t2.content
            else failwith ("Unknown label " ^ lab ^ ".")
        | _ ->
            failwith "Ill-formed projection"
      end
