open Ast.Typ
open Location

type env = (typ, typ kind) Env.t

(* given a type [ty] of kind [Sigma f] and a projection label [l],
   [select_kind_field l ty f] computes the kind of [ty.l] *)
let rec select_kind_field label ty = function
  | [] -> raise Not_found
  | (label', (_, k)) :: _ when Label.equal label.content label' -> k
  | (label', (x, _)) :: f ->
      select_kind_field label ty
        (bsubst_kind_fields f x (dummy_locate (Proj(ty, dummy_locate label'))))

(* given a type [ty] of kind [Sigma f],
   [select_all_fields ty f] computes the map
   [lab -> (ty.l, kind of ty.l) ] *)
let rec select_all_fields ty = function
  | [] -> Label.Map.empty
  | (label, (x, k)) :: f ->
      let ty_lab = dummy_locate (Proj(ty, dummy_locate label)) in
      Label.Map.add label (ty_lab, k)
      (select_all_fields ty (bsubst_kind_fields f x ty_lab))

let rec head_norm env t = match t.content with
| BaseForall(_, _, _) | BaseRecord _ | BaseArrow(_, _) ->
    (t, Some Base)
| FVar x ->
    begin
      let k = Env.get_typ_var x env in
      match k with Single u -> (u, Some k)
      | (Base | Pi(_,_,_) | Sigma _) -> (t, Some k)
    end
| Lam(_,_,_) | Record _ -> (t, None)
| BVar _ -> assert false
| App(t1, t2) ->
    begin
      let (t1', k) = head_norm env t1 in
      match (t1'.content, k) with
      | (Lam (x, _tau, t), None) ->
          head_norm env (bsubst_typ t x t2)
      | ((FVar _ | App(_,_) | Proj(_,_)), Some (Pi(x, _, k1))) ->
          begin
            match bsubst_kind k1 x t2 with
            | Single u -> (u , Some k1)
            | (Base | Pi(_,_,_) | Sigma _) ->
                ({ t with content = App(t1', t2) } , Some k1)
          end
      | ((FVar _ | BVar _ | App(_,_) | Proj(_,_) | Lam(_,_,_) |
        Record _ | BaseArrow (_, _) | BaseRecord _ | BaseForall (_, _, _)),
         (None |
         Some (Base | Single _ | Pi(_,_,_) | Sigma _))) -> assert false
    end
| Proj(t', lab) ->
    begin
      let (t', k) = head_norm env t' in
      match (t'.content, k) with
      | (Record m, None) ->
          begin
            try head_norm env (Label.Map.find lab.content m)
            with Not_found ->
              Error.raise_error Error.syntax t.startpos t.endpos
                ("Illegal label projection: " ^ lab.content ^ ".")
          end
      | ((FVar _ | App(_,_) | Proj(_,_)), Some (Sigma f)) ->
          begin
            try
              match select_kind_field lab t' f with
              | (Single u) as k -> (u, Some k)
              | (Base | Pi(_,_,_) | Sigma _) as k ->
                  ({ t with content = Proj(t', lab) }, Some k)
            with Not_found ->
              Error.raise_error Error.syntax t.startpos t.endpos
                ("Illegal label projection: " ^ lab.content ^ ".")
          end
      | ((FVar _ | BVar _ | BaseArrow (_, _) | BaseRecord _ |
        BaseForall (_, _, _) | Lam (_, _, _) | App(_,_) |
        Proj(_,_) | Record _),
         (None |
         Some (Base | Single _ | Pi(_,_,_) | Sigma _))) -> assert false
    end

let rec path_norm env t = match t.content with
  | BaseRecord m ->
      let m' = Label.Map.map (fun t -> typ_norm env t Base) m in
      ({ t with content = BaseRecord m' }, Base)
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
  | BVar _ | Lam (_,_,_) | Record _ -> assert false
  | App(p, t) ->
      begin
        let (p', k) = path_norm env p in
        match k with
        | Pi(x, k1, k2) ->
            let t' = typ_norm env t k1 in
            ({ t with content = App(p', t') }, bsubst_kind k2 x t)
        | Base | Single _ | Sigma _ -> assert false
      end
  | Proj(p, lab) ->
      begin
        let (p', k) = path_norm env p in
        match k with
        | Sigma f ->
            begin
              try
                ({ t with content = Proj(p', lab) }, select_kind_field lab p f)
              with Not_found ->
                Error.raise_error Error.syntax t.startpos t.endpos
                  ("Illegal label projection: " ^ lab.content ^ ".")
            end
        | Base | Single _ | Pi(_,_,_) -> assert false
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
| Sigma f ->
    let projections = select_all_fields t f in
    { t with content = Record
        (Label.Map.map (fun (t_l, k_l) -> typ_norm env t_l k_l) projections) }

and kind_norm env = function
  | Base -> Base
  | Single t -> Single (typ_norm env t Base)
  | Pi(x, k1, k2) ->
      let k1' = kind_norm env k1
      and y = Var.bfresh x in
      let y_var = dummy_locate (FVar y) in
      let k2' = kind_norm (Env.add_typ_var y k1 env) (bsubst_kind k2 x y_var) in
      mkPi y k1' k2'
  | Sigma f ->
      let f' = kind_fields_norm env f in
      mkSigma f'

and kind_fields_norm env = function
  | [] -> []
  | (lab, (x, k)) :: f ->
      let k' = kind_norm env k
      and y = Var.bfresh x in
      let y_var = dummy_locate (FVar y) in
      let f' =
        kind_fields_norm (Env.add_typ_var y k env)
          (bsubst_kind_fields f x y_var)
      in (lab, (y, k')) :: f'

let rec try_equiv_typ env t1 t2 k =
  let open Answer in
  match k with
  | Base ->
      let (p1, _) = head_norm env t1
      and (p2, _) = head_norm env t2 in
      begin
        match equiv_path env p1 p2 with
        | WithValue.Yes Base -> Yes
        | WithValue.Yes (Single _ | Pi(_,_,_) | Sigma _) -> assert false
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
  | Sigma f ->
      let projections = select_all_fields t1 f in
      Label.Map.fold
        (fun lab (t1_lab, k_lab) acc ->
          acc &*&
          let t2_lab = dummy_locate (Proj(t2, dummy_locate lab)) in
          equiv_typ env t1_lab t2_lab k_lab)
        projections Yes

and equiv_typ env t1 t2 k =
  let open Answer in
  match try_equiv_typ env t1 t2 k with
  | Yes -> Yes
  | No reasons -> No (TYPES (t1, t2) :: reasons)


and equiv_path env p1 p2 =
  let open Answer in
  match (p1.content, p2.content) with
  | (BaseRecord m, BaseRecord m') ->
      equiv_bindings env (Label.Map.bindings m) (Label.Map.bindings m')
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
        | WithValue.Yes (Base | Single _ | Sigma _) -> assert false
        | WithValue.No reasons -> WithValue.No reasons
      end
  | (Proj(t, lab), Proj(t', lab')) when Label.equal lab.content lab'.content ->
      begin
        match equiv_path env t t' with
        | WithValue.Yes (Sigma f) -> WithValue.Yes (select_kind_field lab t f)
        | WithValue.Yes (Base | Single _ | Pi(_,_,_)) -> assert false
        | WithValue.No reasons -> WithValue.No reasons
      end
  | ((FVar _ | BVar _ | Proj (_, _) | Record _ | Lam (_, _, _) |
    App (_, _) | BaseForall (_, _, _) | BaseArrow (_, _) | BaseRecord _),
     _) -> WithValue.No []

and equiv_bindings env b1 b2 =
  let open Answer in match (b1, b2) with
  | ([], []) -> WithValue.Yes Base
  | ([], b) | (b, []) ->
      WithValue.No
        [TYPES
           (dummy_locate (BaseRecord Label.Map.empty),
            dummy_locate
              (BaseRecord
                 (List.fold_left
                    (fun acc (lab, t) -> Label.Map.add lab t acc)
                    Label.Map.empty b)))]
  | ((lab1, t1) :: _, (lab2, t2) :: _) when not (Label.equal lab1 lab2) ->
      WithValue.No
        [TYPES
           (dummy_locate (BaseRecord (Label.Map.singleton lab1 t1)),
            dummy_locate (BaseRecord (Label.Map.singleton lab1 t2)))]
  | ((lab1, t1) :: b1, (lab2, t2) :: b2) (* lab1 = lab2 *) ->
      begin
        match equiv_typ env t1 t2 Base with
        | Yes -> equiv_bindings env b1 b2
        | No reasons ->
            WithValue.No
              (TYPES
                 (dummy_locate (BaseRecord (Label.Map.singleton lab1 t1)),
                  dummy_locate (BaseRecord (Label.Map.singleton lab2 t2)))
               :: reasons)
      end

and equiv_kind env k1 k2 =
  let open Answer in
  sub_kind env k1 k2 &*& sub_kind env k2 k1

and sub_kind env k1 k2 =
  let x = Var.fresh () in
  let x_var = dummy_locate (FVar x) in
  check_sub_kind (Env.add_typ_var x k1 env) x_var k1 k2

and check_sub_kind env p k k' =
  let open Answer in match (k, k') with
  | ((Base | Single _), Base) -> Yes
  | (Base, Single t') -> equiv_typ env p t' Base
  | (Single t, Single t') -> equiv_typ env t t' Base
  | (Pi(x, k1, k2), Pi(x', k1', k2')) ->
      sub_kind env k1' k1 &*&
      let y = Var.bfresh x in
      let y_var = dummy_locate (FVar y) in
      check_sub_kind (Env.add_typ_var y k1' env)
        (dummy_locate (App(p, y_var)))
        (bsubst_kind k2  x  y_var)
        (bsubst_kind k2' x' y_var)
  | (Sigma f, Sigma f') ->
      let projections  = select_all_fields p f
      and projections' = select_all_fields p f' in
      (* for all l ∈ dom f', env ⊢ f(l) ≤ f'(l) *)
      Label.Map.fold
        (fun lab (p_lab, k'_lab) acc ->
          acc &*&
          try
            let (_, k_lab) = Label.Map.find lab projections in
            check_sub_kind env p_lab k_lab k'_lab
          with Not_found ->
            No [KINDS
                  (mkSigma [(lab, (Var.fresh (), k'_lab))], mkSigma [])])
        projections' Yes
  | ((Base | Single _ | Sigma _ | Pi(_,_,_)), _) -> No [KINDS (k, k')]




let equiv_typ_b env t1 t2 k =
  Answer.to_bool (equiv_typ env t1 t2 k)
let equiv_kind_b env k1 k2 =
  Answer.to_bool (equiv_kind env k1 k2)
let sub_kind_b env k1 k2 =
  Answer.to_bool (sub_kind env k1 k2)
