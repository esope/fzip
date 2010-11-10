open Ast
open Ast.Typ
open Location

let option_map f = function
  | None -> None
  | Some x -> Some (f x)

type env = (typ, typ kind) Env.t

(* given a type [ty] of kind [Sigma f] and a projection label [l],
   [select_kind_field l ty f] computes the kind of [ty.l] *)
let rec select_kind_field label ty = function
  | [] -> raise Not_found
  | (label', (_, k)) :: _ when Label.equal label.content label' -> k
  | (label', (x, _)) :: f ->
      select_kind_field label ty
        (Kind.bsubst_fields f x (dummy_locate (Proj(ty, dummy_locate label'))))

(* given a type [ty] of kind [Sigma f],
   [select_all_fields ty f] computes the map
   [lab -> (ty.l, kind of ty.l) ] *)
let rec select_all_fields ty = function
  | [] -> Label.Map.empty
  | (label, (x, k)) :: f ->
      let ty_lab = dummy_locate (Proj(ty, dummy_locate label)) in
      Label.Map.add label (ty_lab, k)
      (select_all_fields ty (Kind.bsubst_fields f x ty_lab))

let rec hd_norm_singleton_fields f t = match f with
| [] -> []
| (lab, (x, k)) :: f ->
    let t_lab = dummy_locate (Proj(t, dummy_locate lab)) in
    let k' = Single(t_lab, k) in
    let y = Var.bfresh x in
    let f' = hd_norm_singleton_fields (Kind.bsubst_fields f x t_lab) t in
    (lab, (y, k')) :: f'

let rec hd_norm_singleton k t = match k with
| Base | Single (_, Base) -> Single(t, Base)
| Single(t', k') ->
    hd_norm_singleton (hd_norm_singleton k' t') t
| Pi(y, k1, k2) ->
    let x = Var.bfresh y in
    let x_var = dummy_locate (FVar x) in
    let t' = dummy_locate (App(t, x_var))
    and k' = Kind.bsubst k2 y x_var in
    Kind.mkPi x k1 (Single(t', k'))
| Sigma f ->
    Kind.mkSigma (hd_norm_singleton_fields f t)

let simplify_kind = function
  | Single(t, k) -> hd_norm_singleton k t
  | (Base | Pi(_,_,_) | Sigma _) as k -> k

let rec head_norm env t = match t.content with
| BaseForall(_, _, _) | BaseExists (_,_,_) | BaseRecord _ | BaseArrow(_, _) ->
    (t, Some Base)
| FVar x ->
    begin
      try
        let k = simplify_kind (Env.Typ.get_var x env) in
        match k with
        | Single (u, Base) -> (u, Some k)
        | Single (_, _) -> assert false
        | (Base | Pi(_,_,_) | Sigma _) -> (t, Some k)
      with Not_found -> assert false
    end
| Lam(_,_,_) | Record _ -> (t, None)
| BVar _ -> assert false
| App(t1, t2) ->
    begin
      let (t1', k) = head_norm env t1 in
      match (t1'.content, option_map simplify_kind k) with
      | (Lam (x, _tau, t), None) ->
          head_norm env (bsubst t x t2)
      | ((FVar _ | App(_,_) | Proj(_,_)), Some (Pi(x, _, k1))) ->
          begin
            match Kind.bsubst k1 x t2 with
            | Single (u, Base) -> (u , Some k1)
            | Single (_, _) -> assert false
            | (Base | Pi(_,_,_) | Sigma _) ->
                ({ t with content = App(t1', t2) } , Some k1)
          end
      | ((FVar _ | BVar _ | App(_,_) | Proj(_,_) | Lam(_,_,_) |
        Record _ | BaseArrow (_, _) | BaseRecord _ |
        BaseForall (_, _, _) | BaseExists (_, _, _)),
         (None |
         Some (Base | Single (_,_) | Pi(_,_,_) | Sigma _))) -> assert false
    end
| Proj(t', lab) ->
    begin
      let (t', k) = head_norm env t' in
      match (t'.content, option_map simplify_kind k) with
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
              match simplify_kind (select_kind_field lab t' f) with
              | (Single (u, Base)) as k -> (u, Some k)
              | Single (_, _) -> assert false
              | (Base | Pi(_,_,_) | Sigma _) as k ->
                  ({ t with content = Proj(t', lab) }, Some k)
            with Not_found ->
              Error.raise_error Error.syntax t.startpos t.endpos
                ("Illegal label projection: " ^ lab.content ^ ".")
          end
      | ((FVar _ | BVar _ | BaseArrow (_, _) | BaseRecord _ |
        BaseForall (_, _, _) | BaseExists (_,_,_) | Lam (_, _, _) | App(_,_) |
        Proj(_,_) | Record _),
         (None |
         Some (Base | Single (_,_) | Pi(_,_,_) | Sigma _))) -> assert false
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
        typ_norm (Env.Typ.add_var x' k1.content env)
          (bsubst t1 x x_var') Base in
      ({ t with content = mkBaseForall x' k1' t1' }, Base)
  | BaseExists (x, k1, t1) ->
      let k1' = { k1 with content = kind_norm env k1.content } in
      let x' = Var.bfresh x in
      let x_var' = dummy_locate (FVar x') in
      let t1' =
        typ_norm (Env.Typ.add_var x' k1.content env)
          (bsubst t1 x x_var') Base in
      ({ t with content = mkBaseExists x' k1' t1' }, Base)
  | FVar x ->
      begin
        try (t, Env.Typ.get_var x env)
        with Not_found -> assert false
      end
  | BVar _ | Lam (_,_,_) | Record _ -> assert false
  | App(p, t) ->
      begin
        let (p', k) = path_norm env p in
        match simplify_kind k with
        | Pi(x, k1, k2) ->
            let t' = typ_norm env t k1 in
            ({ t with content = App(p', t') }, Kind.bsubst k2 x t)
        | Base | Single (_,_) | Sigma _ -> assert false
      end
  | Proj(p, lab) ->
      begin
        let (p', k) = path_norm env p in
        match simplify_kind k with
        | Sigma f ->
            begin
              try
                ({ t with content = Proj(p', lab) }, select_kind_field lab p f)
              with Not_found ->
                Error.raise_error Error.syntax t.startpos t.endpos
                  ("Illegal label projection: " ^ lab.content ^ ".")
            end
        | Base | Single (_,_) | Pi(_,_,_) -> assert false
      end

and typ_norm env t k = match simplify_kind k with
| Base | Single (_,Base) ->
    let (t', _) = head_norm env t in
    let (t'', k'') = path_norm env t' in
    assert (Ast.Kind.equal k'' Base) ;
    t''
| Single (_, _) -> assert false
| Pi(y, k1, k2) ->
    let k1' = dummy_locate (kind_norm env k1) in
    let x = Var.bfresh y in
    let x_var = dummy_locate (FVar x) in
    let t_ext = dummy_locate (App(t, x_var)) in
    let t' =
      typ_norm (Env.Typ.add_var x k1 env) t_ext (Kind.bsubst k2 y x_var) in
    { t with content = mkLam x k1' t' }
| Sigma f ->
    let projections = select_all_fields t f in
    { t with content = Record
        (Label.Map.map (fun (t_l, k_l) -> typ_norm env t_l k_l) projections) }

and kind_norm env = function
  | Base -> Base
  | Single (t, Base) -> Single (typ_norm env t Base, Base)
  | Single (t, k) -> kind_norm env (hd_norm_singleton k t)
  | Pi(x, k1, k2) ->
      let k1' = kind_norm env k1
      and y = Var.bfresh x in
      let y_var = dummy_locate (FVar y) in
      let k2' = kind_norm (Env.Typ.add_var y k1 env) (Kind.bsubst k2 x y_var) in
      Kind.mkPi y k1' k2'
  | Sigma f ->
      let f' = kind_fields_norm env f in
      Kind.mkSigma f'

and kind_fields_norm env = function
  | [] -> []
  | (lab, (x, k)) :: f ->
      let k' = kind_norm env k
      and y = Var.bfresh x in
      let y_var = dummy_locate (FVar y) in
      let f' =
        kind_fields_norm (Env.Typ.add_var y k env)
          (Kind.bsubst_fields f x y_var)
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
        | WithValue.Yes (Single (_,_) | Pi(_,_,_) | Sigma _) -> assert false
        | WithValue.No reasons -> No reasons
      end
  | Single (_,_) -> Yes (* used to be on Single(_,Base) only *)
  | Pi(x, k1, k2) ->
      let y = Var.bfresh x in
      let y_var = dummy_locate (FVar y) in
      equiv_typ (Env.Typ.add_var y k1 env)
        (dummy_locate (App(t1, y_var)))
        (dummy_locate (App(t2, y_var)))
        (Kind.bsubst k2 x y_var)
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
  | (BaseForall(x, k, t), BaseForall(x', k', t'))
  | (BaseExists(x, k, t), BaseExists(x', k', t')) ->
      begin
        match
          equiv_kind env k.content k'.content &*&
          let y = Var.bfresh x in
          let y_var = dummy_locate (FVar y) in
          equiv_typ (Env.Typ.add_var y k.content env)
            (bsubst t x y_var) (bsubst t' x' y_var) Base
        with
        | Yes -> WithValue.Yes Base
        | No reasons -> WithValue.No reasons
      end
  | (FVar x, FVar x') ->
      if Var.equal x x'
      then
        begin
          try WithValue.Yes (Env.Typ.get_var x env)
          with Not_found -> assert false
        end
      else WithValue.No []
  | (App(p, t), App(p', t')) ->
      begin
        match WithValue.map simplify_kind (equiv_path env p p') with
        | WithValue.Yes (Pi(x, k1, k2)) ->
            begin
              match equiv_typ env t t' k1 with
              | Yes -> WithValue.Yes (Kind.bsubst k2 x t)
              | No reasons -> WithValue.No reasons
            end
        | WithValue.Yes (Base | Single (_,_) | Sigma _) -> assert false
        | WithValue.No reasons -> WithValue.No reasons
      end
  | (Proj(t, lab), Proj(t', lab')) when Label.equal lab.content lab'.content ->
      begin
        match WithValue.map simplify_kind (equiv_path env t t') with
        | WithValue.Yes (Sigma f) -> WithValue.Yes (select_kind_field lab t f)
        | WithValue.Yes (Base | Single (_,_) | Pi(_,_,_)) -> assert false
        | WithValue.No reasons -> WithValue.No reasons
      end
  | ((FVar _ | BVar _ | Proj (_, _) | Record _ | Lam (_, _, _) |
    App (_, _) | BaseForall (_, _, _) | BaseExists (_,_,_) |
    BaseArrow (_, _) | BaseRecord _),
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
  check_sub_kind (Env.Typ.add_var x k1 env) x_var
    (simplify_kind k1) (simplify_kind k2)

and try_check_sub_kind env p k k' =
  let open Answer in
  match (simplify_kind k, simplify_kind k') with
  | ((Base | Single (_, Base)), Base) -> Yes
  | (Base, Single (t', Base)) -> equiv_typ env p t' Base
  | (Single (t, Base), Single (t', Base)) -> equiv_typ env t t' Base
  | (Single (_, (Single(_,_) | Pi(_,_,_) | Sigma _)), _)
  | (_, Single (_,_)) -> assert false (* kinds are simplified by sub_kind *)
  | (Pi(x, k1, k2), Pi(x', k1', k2')) ->
      sub_kind env k1' k1 &*&
      let y = Var.bfresh x in
      let y_var = dummy_locate (FVar y) in
      check_sub_kind (Env.Typ.add_var y k1' env)
        (dummy_locate (App(p, y_var)))
        (Kind.bsubst k2  x  y_var)
        (Kind.bsubst k2' x' y_var)
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
                  (Kind.mkSigma
                     [(lab, (Var.fresh (), k'_lab))], Kind.mkSigma [])])
        projections' Yes
  | ((Base | Single (_, Base) | Sigma _ | Pi(_,_,_)), _) -> No []

and check_sub_kind env p k k' =
  let open Answer in
  match try_check_sub_kind env p k k' with
  | Yes -> Yes
  | No reasons -> No (KINDS (k,k') :: reasons)


let equiv_typ_b env t1 t2 k =
  Answer.to_bool (equiv_typ env t1 t2 k)
let equiv_kind_b env k1 k2 =
  Answer.to_bool (equiv_kind env k1 k2)
let sub_kind_b env k1 k2 =
  Answer.to_bool (sub_kind env k1 k2)
