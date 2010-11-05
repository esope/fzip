open Ast.Typ
open Location

type env = (typ, typ kind) Env.t

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
      | (_, Some (Pi(x, _, k1))) ->
          begin
            match bsubst_kind k1 x t2 with
            | Single u -> (u , Some k1)
            | _ -> ({ t with content = App(t1', t2) } , Some k1)
          end
      | _ -> assert false
    end
| Proj(t', lab) ->
    begin
      let (t', k) = head_norm env t' in
      match (t'.content, k) with
      | (Pair(t1, t2), None) ->
          begin
            match lab.content with
            | "fst" -> head_norm env t1
            | "snd" -> head_norm env t2
            | _ -> Error.raise_error Error.syntax t.startpos t.endpos
                  ("Illegal label projection: " ^ lab.content ^ ".")
          end
      | (_, Some (Sigma (x, k1, k2))) ->
          begin
            match lab.content with
            | "fst" ->
                begin
                  match k1 with
                  | Single u ->
                      (u, Some k1)
                  | _ ->
                      ({ t with content = Proj(t', lab) }, Some k1)
                end
            | "snd" ->
                begin
                  match bsubst_kind k2 x
                      (dummy_locate (Proj(t, dummy_locate "fst"))) with
                  | Single u ->
                      (u, Some k2)
                  | _ ->
                      ({ t with content = Proj(t', lab) }, Some k2)
                end
            | _ -> Error.raise_error Error.syntax t.startpos t.endpos
                  ("Illegal label projection: " ^ lab.content ^ ".")
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
      let k1' = { k1 with content = kind_norm env k1.content } in
      let x' = Var.bfresh x in
      let x_var' = dummy_locate (FVar x') in
      let t1' =
        typ_norm (Env.add_typ_var x' k1.content env)
          (bsubst_typ t1 x x_var') Base in
      ({ t with content = mkBaseForall x' k1' t1' }, Base)
  | FVar x -> (t, Env.get_typ_var x env)
  | BVar _ | Lam (_,_,_) | Pair(_, _) -> assert false
  | App(p, t) ->
      begin
        let (p', k) = path_norm env p in
        match k with
        | Pi(x, k1, k2) ->
            let t' = typ_norm env t k1 in
            ({ t with content = App(p', t') }, bsubst_kind k2 x t)
        | _ -> assert false
      end
  | Proj(p, lab) ->
      begin
        let (p', k) = path_norm env p in
        match k with
        | Sigma(x, k1, k2) ->
            begin
              match lab.content with
              | "fst" -> ({ t with content = Proj(p', lab) }, k1)
              | "snd" -> ({ t with content = Proj(p', lab) },
                          bsubst_kind k2 x
                            (dummy_locate (Proj(p, dummy_locate "fst"))))
              | _ -> Error.raise_error Error.syntax t.startpos t.endpos
                    ("Illegal label projection: " ^ lab.content ^ ".")
            end
        | _ -> assert false
      end

and typ_norm env t k = match k with
| Base | Single _ ->
    let (t', _) = head_norm env t in
    let (t'', tau) = path_norm env t' in
    assert (tau = Base) ;
    t''
| Pi(y, k1, k2) ->
    let k1' = dummy_locate (kind_norm env k1) in
    let x = Var.bfresh y in
    let x_var = dummy_locate (FVar x) in
    let t_ext = dummy_locate (App(t, x_var)) in
    let t' =
      typ_norm (Env.add_typ_var x k1 env) t_ext (bsubst_kind k2 y x_var) in
    { t with content = mkLam x k1' t' }
| Sigma(y, k1, k2) ->
    let t1 = typ_norm env (dummy_locate (Proj(t, dummy_locate "fst"))) k1 in
    let t2 =
      typ_norm env (dummy_locate (Proj(t, dummy_locate "snd")))
        (bsubst_kind k2 y t1) in
    { t with content = Pair(t1, t2) }

and kind_norm env = function
  | Base -> Base
  | Single t -> Single (typ_norm env t Base)
  | Pi(x, k1, k2) ->
      let k1' = kind_norm env k1
      and y = Var.bfresh x in
      let y_var = dummy_locate (FVar y) in
      let k2' = kind_norm (Env.add_typ_var y k1 env) (bsubst_kind k2 x y_var) in
      mkPi y k1' k2'
  | Sigma(x, k1, k2) ->
      let k1' = kind_norm env k1
      and y = Var.bfresh x in
      let y_var = dummy_locate (FVar y) in
      let k2' = kind_norm (Env.add_typ_var y k1 env) (bsubst_kind k2 x y_var) in
      mkSigma y k1' k2'

let equiv_typ_simple env t1 t2 k =
  let open Answer in
  if eq_typ (typ_norm env t1 k) (typ_norm env t2 k)
  then Yes
  else No [TYPES (t1, t2)]

let rec try_equiv_typ env t1 t2 k =
  let open Answer in
  match k with
  | Base ->
      let (p1, _) = head_norm env t1
      and (p2, _) = head_norm env t2 in
      begin
        match equiv_path env p1 p2 with
        | WithValue.Yes Base -> Yes
        | WithValue.Yes _ -> assert false
        | WithValue.No reasons -> No reasons
      end
  | Single _ -> Yes
  | Pi(x, k1, k2) ->
      let y = Var.bfresh x in
      let y_var = dummy_locate (FVar y) in
      equiv_typ (Env.add_typ_var y k1 env)
        (dummy_locate (App(t1, y_var)))
        (dummy_locate (App(t2, y_var)))
        (bsubst_kind k2 x y_var)
  | Sigma(x, k1, k2) ->
      let t1_1 = dummy_locate (Proj(t1, dummy_locate "fst")) in
      equiv_typ env
        t1_1
        (dummy_locate (Proj(t2, dummy_locate "fst")))
        k1 &*&
      equiv_typ env
        (dummy_locate (Proj(t1, dummy_locate "snd")))
        (dummy_locate (Proj(t2, dummy_locate "snd")))
        (bsubst_kind k2 x t1_1)

and equiv_typ env t1 t2 k =
  let open Answer in
  match try_equiv_typ env t1 t2 k with
  | Yes -> Yes
  | No reasons -> No (TYPES (t1, t2) :: reasons)


and equiv_path env p1 p2 =
  let open Answer in
  match (p1.content, p2.content) with
  | (BaseProd(t1, t2), BaseProd(t1', t2'))
  | (BaseArrow(t1, t2), BaseArrow(t1', t2')) ->
      begin
        match equiv_typ env t1 t1' Base &*&
          equiv_typ env t2 t2' Base with
        | Yes -> WithValue.Yes Base
        | No reasons -> WithValue.No reasons
      end
  | (BaseForall(x, k, t), BaseForall(x', k', t')) ->
      begin
        match
          equiv_kind env k.content k'.content &*&
          let y = Var.bfresh x in
          let y_var = dummy_locate (FVar y) in
          equiv_typ (Env.add_typ_var y k.content env)
            (bsubst_typ t x y_var) (bsubst_typ t' x' y_var) Base
        with
        | Yes -> WithValue.Yes Base
        | No reasons -> WithValue.No reasons
      end
  | (FVar x, FVar x') ->
      if x = x'
      then WithValue.Yes (Env.get_typ_var x env)
      else WithValue.No []
  | (App(p, t), App(p', t')) ->
      begin
        match equiv_path env p p' with
        | WithValue.Yes (Pi(x, k1, k2)) ->
            begin
              match equiv_typ env t t' k1 with
              | Yes -> WithValue.Yes (bsubst_kind k2 x t)
              | No reasons -> WithValue.No reasons
            end
        | WithValue.Yes _ -> assert false
        | WithValue.No reasons -> WithValue.No reasons
      end
  | (Proj(t, lab), Proj(t', lab'))
    when lab.content = "fst" && lab.content = lab'.content ->
      begin
        match equiv_path env t t' with
        | WithValue.Yes (Sigma(_, k, _)) -> WithValue.Yes k
        | WithValue.Yes _ -> assert false
        | WithValue.No reasons -> WithValue.No reasons
      end
  | (Proj(t, lab), Proj(t', lab'))
    when lab.content = "snd" && lab.content = lab'.content ->
      begin
        match equiv_path env t t' with
        | WithValue.Yes (Sigma(x, _, k)) ->
            let t_1 = dummy_locate (Proj(t, dummy_locate "fst")) in
            WithValue.Yes (bsubst_kind k x t_1)
        | WithValue.Yes _ -> assert false
        | WithValue.No reasons -> WithValue.No reasons
      end
  | _ -> WithValue.No []

and try_equiv_kind env k1 k2 =
  let open Answer in
  match (k1, k2) with
  | (Base, Base) -> Yes
  | (Single t, Single t') -> equiv_typ env t t' Base
  | (Pi(x, k1, k2), Pi(x', k1', k2')) | (Sigma(x, k1, k2), Sigma(x', k1', k2')) ->
      equiv_kind env k1 k1' &*&
      let y = Var.bfresh x in
      let y_var = dummy_locate (FVar y) in
      equiv_kind (Env.add_typ_var y k1 env)
        (bsubst_kind k2 x y_var) (bsubst_kind k2' x' y_var)
  | _ -> No []

and equiv_kind env k1 k2 =
  let open Answer in
  match try_equiv_kind env k1 k2 with
  | Yes -> Yes
  | No reasons -> No (KINDS (k1,k2) :: reasons)

let equiv_typ_b env t1 t2 k =
  Answer.to_bool (equiv_typ env t1 t2 k)
let equiv_typ_simple_b env t1 t2 k =
  Answer.to_bool (equiv_typ_simple env t1 t2 k)
let equiv_kind_b env k1 k2 =
  Answer.to_bool (equiv_kind env k1 k2)
