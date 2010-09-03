open Ast.Typ
open Ast_utils
open Location

let rec single_ext k t = match k with
| Base -> Single t
| Single u as k -> k
| Arrow(k1, k2) ->
    let x = new_var () in
    let x_var = dummy_locate (FVar x) in
    let k2' = single_ext k2 (dummy_locate (App(t, x_var))) in
    mkPi x k1 k2'
| Pi(y, k1, k2) ->
    let x = new_var () in
    let x_var = dummy_locate (FVar x) in
    let k2' =
      single_ext (bsubst_kind k2 y x_var) (dummy_locate (App(t, x_var))) in
    mkPi x k1 k2'
| Prod(k1, k2) ->
    let k1' = single_ext k1 (dummy_locate (Proj(t, "fst")))
    and k2' = single_ext k2 (dummy_locate (Proj(t, "snd"))) in
    Prod(k1', k2')
| Sigma(y, k1, k2) ->
    let t1 = dummy_locate (Proj(t, "fst")) in
    let k1' = single_ext k1 t1
    and k2' = single_ext (bsubst_kind k2 y t1) (dummy_locate (Proj(t, "snd"))) in
    Prod(k1', k2')

let rec wfsub env k1 k2 = match (k1, k2) with
| (Base, Base) | (Single _, Base) -> true
| (Arrow(k1, k2), Arrow(k1', k2')) ->
    wfsub env k1' k1 && wfsub env k2 k2'
| (Pi(x,k1, k2), Pi(x',k1', k2')) ->
    wfsub env k1' k1 &&
    let y = new_var () in
    let y_var = dummy_locate (FVar y) in
    wfsub (Env.add_typ_var y k1' env)
      (bsubst_kind k2 x y_var) (bsubst_kind k2' x' y_var)
| (Arrow(k1, k2), Pi(x', k1', k2')) ->
    wfsub env k1' k1 &&
    let y = new_var () in
    let y_var = dummy_locate (FVar y) in
    wfsub (Env.add_typ_var y k1' env) k2 (bsubst_kind k2' x' y_var)
| (Pi(x, k1, k2), Arrow(k1', k2')) ->
    wfsub env k1' k1 &&
    let y = new_var () in
    let y_var = dummy_locate (FVar y) in
    wfsub (Env.add_typ_var y k1' env) (bsubst_kind k2 x y_var) k2'
| (Prod(k1, k2), Prod(k1', k2')) ->
    wfsub env k1 k1' && wfsub env k2 k2'
| (Sigma(x,k1, k2), Sigma(x',k1', k2')) ->
    wfsub env k1 k1 &&
    let y = new_var () in
    let y_var = dummy_locate (FVar y) in
    wfsub (Env.add_typ_var y k1 env)
      (bsubst_kind k2 x y_var) (bsubst_kind k2' x' y_var)
| (Prod(k1, k2), Sigma(x',k1', k2')) ->
    wfsub env k1 k1 &&
    let y = new_var () in
    let y_var = dummy_locate (FVar y) in
    wfsub (Env.add_typ_var y k1 env) k2 (bsubst_kind k2' x' y_var)
| (Sigma(x,k1, k2), Prod(k1', k2')) ->
    wfsub env k1 k1 &&
    let y = new_var () in
    let y_var = dummy_locate (FVar y) in
    wfsub (Env.add_typ_var y k1 env) (bsubst_kind k2 x y_var) k2
| (Single t, Single t') ->
    let test = Normalize.equiv_typ env t t' Base in
    assert (test = Normalize.equiv_typ_simple env t t' Base) ;
    test
| _ -> failwith
      (Printf.sprintf "Subkinding error:\n  %a\n  is not a subkind of\n  %a"
      (fun () -> PPrint.Kind.string) k1
      (fun () -> PPrint.Kind.string) k2)

let rec wftype env t = match t.content with
| BVar _ -> assert false
| FVar x -> single_ext (Env.get_typ_var x env) t
| App(t1, t2) ->
    let k1 = wftype env t1 and k2 = wftype env t2 in 
    begin
      match k1 with
      | Arrow(k2', k1') ->
          if wfsub env k2 k2'
          then k1'
          else failwith "Ill-kinded application."
      | Pi(x, k2', k1') ->
          if wfsub env k2 k2'
          then bsubst_kind k1' x t2
          else failwith "Ill-kinded application."
      | _ -> failwith "Non functional application."
    end
| Lam(x, k, t) ->
    wfkind env k ;
    let x' = new_var () in
    let t' = bsubst_typ t x (dummy_locate (FVar x')) in
    let k' = wftype (Env.add_typ_var x' k env) t' in
    Arrow(k, k')
| Pair(k1, k2) ->
    let k1 = wftype env k1 
    and k2 = wftype env k2 in
    Prod(k1, k2)
| Proj(t, lab) ->
    let k = wftype env t in
    begin
      match k with
      | Prod(k1, _) | Sigma(_, k1, _) when lab = "fst" -> k1
      | Prod(_, k2) when lab = "snd" -> k2
      | Sigma(x, _, k2) when lab = "snd" ->
          bsubst_kind k2 x (dummy_locate (Proj(t, "fst")))
      | _ -> failwith "Ill-formed projection."
    end
| BaseForall(x, k, u) ->
    wfkind env k ;
    let x' = new_var () in
    let u' = bsubst_typ u x (dummy_locate (FVar x')) in
    let env' = Env.add_typ_var x' k env in
    let k' = wftype env' u' in
    if wfsub env' k' Base
    then Single t
    else failwith "Ill-formed universal type."
| BaseProd(t1, t2) | BaseArrow(t1, t2) ->
    if wfsub env (wftype env t1) Base &&
      wfsub env (wftype env t2) Base
    then Single t
    else failwith "Ill-formed basic product type."

and wfkind env = function
  | Base -> ()
  | Arrow(k1, k2) | Prod(k1, k2) ->
      wfkind env k1 ;
      wfkind env k2
  | Pi(y, k1, k2) | Sigma(y, k1, k2) ->
      wfkind env k1 ;
      let x = new_var () in
      let x_var = dummy_locate (FVar x) in
      wfkind (Env.add_typ_var x k1 env) (bsubst_kind k2 y x_var)
  | Single t ->
      match wftype env t with
      | Single _ | Base -> ()
      | _ -> failwith "Ill-formed singleton."
