open Ast.Typ
open Location

let rec head_norm env t = match t.content with
| BaseForall(_, _, _) | BaseProd(_, _) | BaseArrow(_, _) ->
    (t, Some Base)
| FVar x ->
    begin
      let k = Env.get_typ_var x env in
      match k with Single u -> (u, Some k)
      | _ -> (t, Some k)
    end
| Lam(_,_,_) | Pair(_, _) -> (t, None)
| BVar _ -> assert false
| App(t1, t2) ->
    begin
      let (t1', k) = head_norm env t1 in
      match (t1'.content, k) with
      | (Lam (x, tau, t), None) ->
          head_norm env (bsubst_typ t x t2)
      | (_, Some (Arrow(_, k1))) ->
          begin
            match k1 with
            | Single u -> (u , Some k1)
            | _ -> ({ t with content = App(t1', t2) } , Some k1)
          end
      | (_, Some (Pi(x, _, k1))) ->
          begin
            match bsubst_kind k1 x t2 with
            | Single u -> (u , Some k1)
            | _ -> ({ t with content = App(t1', t2) } , Some k1)
          end
      | _ -> assert false
    end
| Proj(t, lab) ->
    begin
      let (t', k) = head_norm env t in
      match (t'.content, k) with
      | (Pair(t1, t2), None) ->
          begin
            match lab with
            | "1" -> head_norm env t1
            | "2" -> head_norm env t2
            | _ -> failwith "Illegal label projection."
          end
      | (_, Some (Prod (k1, k2))) ->
          begin
            match lab with
            | "1" ->
                begin
                  match k1 with
                  | Single u ->
                      (u, Some k1)
                  | _ ->
                      ({ t with content = Proj(t', lab) }, Some k1)
                end
            | "2" ->
                begin
                  match k2 with
                  | Single u ->
                      (u, Some k2)
                  | _ ->
                      ({ t with content = Proj(t', lab) }, Some k2)
                end
            | _ -> failwith "Illegal label projection."
          end
      | (_, Some (Sigma (x, k1, k2))) ->
          begin
            match lab with
            | "1" ->
                begin
                  match k1 with
                  | Single u ->
                      (u, Some k1)
                  | _ ->
                      ({ t with content = Proj(t', lab) }, Some k1)
                end
            | "2" ->
                begin
                  match bsubst_kind k2 x (dummy_locate (Proj(t, "1"))) with
                  | Single u ->
                      (u, Some k2)
                  | _ ->
                      ({ t with content = Proj(t', lab) }, Some k2)
                end
            | _ -> failwith "Illegal label projection."
          end
      | _ -> assert false
    end

let rec path_norm env t = match t.content with
  | BaseProd(t1, t2) ->
      let t1' = typ_norm env t1 Base
      and t2' = typ_norm env t2 Base in
      ({ t with content = BaseProd(t1', t2') }, Base)
  | BaseArrow(t1, t2) ->
      let t1' = typ_norm env t1 Base
      and t2' = typ_norm env t2 Base in
      ({ t with content = BaseArrow(t1', t2') }, Base)
  | BaseForall (x, k1, t1) ->
      let k1' = kind_norm env k1 in
      let x' = new_var () in
      let x_var' = dummy_locate (FVar x') in
      let t1' =
        typ_norm (Env.add_typ_var x' k1 env) (bsubst_typ t1 x x_var') Base in
      ({ t with content = mkBaseForall x' k1' t1' }, Base)
  | FVar x -> (t, Env.get_typ_var x env)
  | BVar _ | Lam (_,_,_) | Pair(_, _) -> assert false
  | App(p, t) ->
      begin
        let (p', k) = path_norm env p in
        match k with
        | Arrow(k1, k2) ->
            let t' = typ_norm env t k1 in
            ({ t with content = App(p', t') }, k2)
        | _ -> assert false
      end
  | Proj(p, lab) ->
      begin
        let (p', k) = path_norm env p in
        match k with
        | Prod(k1, k2) ->
            begin
              match lab with
              | "1" -> ({ t with content = Proj(p', lab) }, k1)
              | "2" -> ({ t with content = Proj(p', lab) }, k2)
              | _ -> failwith "Illegal label projection."
            end
        | _ -> assert false
      end

and typ_norm env t k = match k with
| Base | Single _ ->
    let (t', _) = head_norm env t in
    let (t'', tau) = path_norm env t' in
    assert (tau = Base) ;
    t''
| Arrow(k1, k2) ->
    let k1' = kind_norm env k1 in
    let x = new_var () in
    let t_ext = dummy_locate (App(t, dummy_locate (FVar x))) in
    let t' = typ_norm (Env.add_typ_var x k1 env) t_ext k2 in
    { t with content = mkLam x k1' t' }
| Pi(y, k1, k2) ->
    let k1' = kind_norm env k1 in
    let x = new_var () in
    let x_var = dummy_locate (FVar x) in
    let t_ext = dummy_locate (App(t, x_var)) in
    let t' =
      typ_norm (Env.add_typ_var x k1 env) t_ext (bsubst_kind k2 y x_var) in
    { t with content = mkLam x k1' t' }
| Prod(k1, k2) ->
    let t1 = typ_norm env (dummy_locate (Proj(t, "1"))) k1
    and t2 = typ_norm env (dummy_locate (Proj(t, "2"))) k2 in
    { t with content = Pair(t1, t2) }
| Sigma(y, k1, k2) ->
    let t1 = typ_norm env (dummy_locate (Proj(t, "1"))) k1 in
    let t2 = typ_norm env (dummy_locate (Proj(t, "2"))) (bsubst_kind k2 y t1) in
    { t with content = Pair(t1, t2) }

and kind_norm env = function
  | Base -> Base
  | Single t -> Single (typ_norm env t Base)
  | Arrow(k1, k2) ->
      let k1' = kind_norm env k1
      and k2' = kind_norm env k2 in
      Arrow(k1', k2')
  | Pi(x, k1, k2) ->
      let k1' = kind_norm env k1
      and y = new_var () in
      let y_var = dummy_locate (FVar y) in
      let k2' = kind_norm (Env.add_typ_var y k1 env) (bsubst_kind k2 x y_var) in
      mkPi y k1' k2'
  | Prod(k1, k2) ->
      let k1' = kind_norm env k1
      and k2' = kind_norm env k2 in
      Prod(k1', k2')
  | Sigma(x, k1, k2) ->
      let k1' = kind_norm env k1
      and y = new_var () in
      let y_var = dummy_locate (FVar y) in
      let k2' = kind_norm (Env.add_typ_var y k1 env) (bsubst_kind k2 x y_var) in
      mkSigma y k1' k2'

let equiv_typ_simple env t1 t2 k =
  eq_typ (typ_norm env t1 k) (typ_norm env t2 k)

let rec equiv_typ env t1 t2 k = match k with
| Base ->
    let (p1, _) = head_norm env t1
    and (p2, _) = head_norm env t2 in
    begin
      match equiv_path env p1 p2 with
      | Some Base -> true
      | Some _ -> assert false
      | None -> false
    end
| Single _ -> true
| Pi(x, k1, k2) ->
    let y = new_var () in
    let y_var = dummy_locate (FVar y) in
    equiv_typ (Env.add_typ_var y k1 env)
      (dummy_locate (App(t1, y_var)))
      (dummy_locate (App(t2, y_var)))
      (bsubst_kind k2 x y_var)
| Arrow(k1, k2) ->
    let y = new_var () in
    let y_var = dummy_locate (FVar y) in
    equiv_typ (Env.add_typ_var y k1 env)
      (dummy_locate (App(t1, y_var)))
      (dummy_locate (App(t2, y_var)))
      k2
| Sigma(x, k1, k2) ->
    let t1_1 = dummy_locate (Proj(t1,"1")) in
    equiv_typ env
      t1_1
      (dummy_locate (Proj(t2,"1")))
      k1 &&
    equiv_typ env
      (dummy_locate (Proj(t1,"2")))
      (dummy_locate (Proj(t2,"2")))
      (bsubst_kind k2 x t1_1)
| Prod(k1, k2) ->
    equiv_typ env
      (dummy_locate (Proj(t1,"1")))
      (dummy_locate (Proj(t2,"1")))
      k1 &&
    equiv_typ env
      (dummy_locate (Proj(t1,"2")))
      (dummy_locate (Proj(t2,"2")))
      k2

and equiv_path env p1 p2 = pre_equiv_path env p1.content p2.content
and pre_equiv_path env p1 p2 = match (p1, p2) with
| (BaseProd(t1, t2), BaseProd(t1', t2')) ->
    if equiv_typ env t1 t1' Base &&
      equiv_typ env t2 t2' Base
    then Some Base
    else None
| (BaseForall(x, k, t), BaseForall(x', k', t')) ->
    if equiv_kind env k k' &&
      let y = new_var () in
      let y_var = dummy_locate (FVar y) in
      equiv_typ (Env.add_typ_var y k env)
        (bsubst_typ t x y_var) (bsubst_typ t' x' y_var) Base
    then Some Base
    else None
| (FVar x, FVar x') ->
    if x = x'
    then Some (Env.get_typ_var x env)
    else None
| (App(p, t), App(p', t')) ->
    begin
      match equiv_path env p p' with
      | Some (Arrow(k1, k2)) ->
          if equiv_typ env t t' k1
          then Some k2
          else None
      | Some (Pi(x, k1, k2)) ->
          if equiv_typ env t t' k1
          then Some (bsubst_kind k2 x t)
          else None
      | Some _ -> assert false
      | None -> None
    end
| (Proj(t, lab), Proj(t', lab')) when lab = "1" && lab = lab' ->
    begin
      match equiv_path env t t' with
      | Some (Prod(k, _) | Sigma(_, k, _)) -> Some k
      | Some _ -> assert false
      | None -> None
    end
| (Proj(t, lab), Proj(t', lab')) when lab = "2" && lab = lab' ->
    begin
      match equiv_path env t t' with
      | Some (Prod(_, k)) -> Some k
      | Some (Sigma(x, _, k)) ->
          let t_1 = dummy_locate (Proj(t,"1")) in
          Some (bsubst_kind k x t_1)
      | Some _ -> assert false
      | None -> None
    end
| _ -> assert false

and equiv_kind env k1 k2 = match (k1, k2) with
| (Base, Base) -> true
| (Single t, Single t') -> equiv_typ env t t' Base
| (Arrow(k1, k2), Arrow(k1', k2')) ->
    equiv_kind env k1 k1' && equiv_kind env k2 k2'
| (Pi(x, k1, k2), Pi(x', k1', k2')) | (Sigma(x, k1, k2), Sigma(x', k1', k2')) ->
    equiv_kind env k1 k1' &&
    let y = new_var () in
    let y_var = dummy_locate (FVar y) in
    equiv_kind (Env.add_typ_var y k1 env)
      (bsubst_kind k2 x y_var) (bsubst_kind k2' x' y_var)
| (Arrow(k1, k2), Pi(x', k1', k2')) | (Prod(k1, k2), Sigma(x', k1', k2')) ->
    equiv_kind env k1 k1' &&
    let y = new_var () in
    let y_var = dummy_locate (FVar y) in
    equiv_kind (Env.add_typ_var y k1 env) k2 (bsubst_kind k2' x' y_var)
| (Pi(x, k1, k2), Arrow(k1', k2')) | (Sigma(x, k1, k2), Prod(k1', k2')) ->
    equiv_kind env k1 k1' &&
    let y = new_var () in
    let y_var = dummy_locate (FVar y) in
    equiv_kind (Env.add_typ_var y k1 env) (bsubst_kind k2 x y_var) k2'
| _ -> false
