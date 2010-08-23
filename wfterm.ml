open Ast
open Term
open Wftype
open Location

let dummy_locate = dummy_locate
let wfsub_kind = Wftype.wfsub
let wfsub env tau1 tau2 = Normalize.equiv_typ env tau1 tau2 Typ.Base
let wfbasetype env t =
  wfsub_kind env (wftype env t) Typ.Base

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
            if wfsub env tau2 tau2'
            then tau1'.content
            else failwith "Ill-formed application (subtyping error)."
        | _ ->
            failwith "Non functional application."
      end
  | Gen (x, k, e) ->
      wfkind env k ;
      let x' = Typ.new_var () in
      let x_var' = dummy_locate (Typ.FVar x') in
      let t' = wfterm (Env.add_typ_var x' k env) (bsubst_typ_var e x x_var') in
      Typ.mkBaseForall x' k t'
  | Inst(e, tau) ->
    begin
      match (wfterm env e).content with
      | Typ.BaseForall(x, k', tau') ->
          let k = wftype env tau in
          if wfsub_kind env k k'
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
            if lab = "1" then t1.content
            else if lab = "2" then t2.content
            else failwith ("Unknown label " ^ lab ^ ".")
        | _ ->
            failwith "Ill-formed projection"
      end
