open Ast
open Ast.Typ
open Location

let sub_kind = Normalize.sub_kind
let sub_kind_b = Normalize.sub_kind_b

let rec wftype env t =
  let open Answer in
  match t.content with
  | BVar _ -> assert false
  | FVar x ->
      begin
        try Kind.mkSingle t (snd (Env.Typ.get_var x env))
        with Not_found ->
          Error.raise_error Error.type_wf t.startpos t.endpos
            (Printf.sprintf "Unbound type variable: %s." (Var.to_string x))
        | Env.Removed_var loc ->
            Error.raise_error Error.type_wf t.startpos t.endpos
              (Printf.sprintf "The type variable %s cannot be used since the program point in %s."
                 (Var.to_string x) (location_msg loc))
      end
  | App(t1, t2) ->
      let k1 = wftype env t1 and k2 = wftype env t2 in
      begin
        match Normalize.simplify_kind k1 with
        | Pi(x, k2', k1') ->
            begin
              match sub_kind ~unfold_eq:false env k2 k2' with
              | Yes -> Kind.bsubst k1' x t2
              | No reasons ->
                  Error.raise_error Error.type_wf t.startpos t.endpos
                    (Printf.sprintf "Ill-kinded application:\n%s%!"
                       (error_msg reasons))
            end
        | Base | Single (_,_) | Sigma _ ->
            Error.raise_error Error.type_wf t.startpos t.endpos
              "Non functional application."
      end
  | Lam({ content = x ; _ } as x_loc, k, t) ->
      if wfkind env k.content
      then
        let x' = Var.bfresh x in
        let t' = bsubst t x (dummy_locate (mkVar x')) in
        let k' =
          wftype
            (Env.Typ.add_var (locate_with Mode.U x_loc) x' k.content env)
            t' in
        Kind.mkPi x' k.content k'
      else
        Error.raise_error Error.kind_wf k.startpos k.endpos "Ill-formed kind."
  | Record m ->
      let x = Var.fresh () in
      let f = Label.Map.fold
          (fun lab t acc -> (lab, (x, wftype env t)) :: acc)
          m []
      in Kind.mkSigma f
  | Proj(t', lab) ->
      begin
        match Normalize.simplify_kind (wftype env t') with
        | Sigma f ->
            begin
              try Normalize.select_kind_field lab t' f
              with Not_found ->
                Error.raise_error Error.type_wf t.startpos t.endpos
                  (Printf.sprintf
                     "Ill-formed projection: unknown label %s." lab.content)
            end
        | Base | Single (_,Base) | Pi(_,_,_) ->
            Error.raise_error Error.type_wf t.startpos t.endpos
              "Ill-formed projection."
        | Single (_,_) -> assert false
      end
  | BaseForall({ content = x ; _ } as x_loc, k, u)
  | BaseExists({ content = x ; _ } as x_loc, k, u) ->
      if wfkind env k.content
      then
        let x' = Var.bfresh x in
        let u' = bsubst u x (dummy_locate (mkVar x')) in
        let env' =
          Env.Typ.add_var (locate_with Mode.U x_loc) x' k.content env in
        let k' = wftype env' u' in
        let open Kind in
        if sub_kind_b ~unfold_eq:false env' k' mkBase
        then mkSingle t mkBase
        else Error.raise_error Error.type_wf k.startpos k.endpos
            "Ill-formed universal type: this kind is not a base kind."
      else Error.raise_error Error.kind_wf k.startpos k.endpos
          "Ill-formed kind."
  | BaseArrow(t1, t2) ->
      begin
        let open Kind in
        if sub_kind_b ~unfold_eq:false env (wftype env t1) mkBase
        then if sub_kind_b ~unfold_eq:false env (wftype env t2) mkBase
        then mkSingle t mkBase
        else Error.raise_error Error.type_wf t2.startpos t2.endpos
            "Ill-formed basic arrow type: this type has not a base kind."
        else Error.raise_error Error.type_wf t1.startpos t1.endpos
            "Ill-formed basic arrow type: this type has not a base kind."
      end
  | BaseRecord m ->
      Label.Map.iter
        (fun _lab t ->
          if sub_kind_b ~unfold_eq:false env (wftype env t) Kind.mkBase
          then ()
          else Error.raise_error Error.type_wf t.startpos t.endpos
              "Ill-formed basic record type: this type has not a base kind.")
        m ;
      Kind.(mkSingle t mkBase)

and wfkind env = function
  | Base -> true
  | Sigma f -> wfkind_fields env f
  | Pi(y, k1, k2) ->
      wfkind env k1 &&
      let x = Var.bfresh y in
      let x_var = dummy_locate (mkVar x) in
      wfkind
        (Env.Typ.add_var (dummy_locate Mode.U) x k1 env)
        (Kind.bsubst k2 y x_var)
  | Single (t, k) ->
      if wfkind env k
      then
        let k' = wftype env t in
        let open Answer in
        match sub_kind ~unfold_eq:false env k' k with
        | Yes -> true
        | No reasons ->
            Error.raise_error Error.kind_wf t.startpos t.endpos
              (Printf.sprintf "Ill-formed singleton:\n%s%!"
                 (error_msg (WF_TYPE (t, k) :: reasons)))
      else
        Error.raise_error Error.kind_wf t.startpos t.endpos
          ("Ill-formed singleton: the given kind is ill-formed.\n")

and wfkind_fields env = function
  | [] -> true
  | (_lab, (x, k)) :: f ->
      wfkind env k &&
      let y = Var.bfresh x in
      let y_var = dummy_locate (mkVar y) in
      wfkind_fields
        (Env.Typ.add_var (dummy_locate Mode.U) y k env)
        (Kind.bsubst_fields f x y_var)

let rec try_sub_type ~unfold_eq env tau tau' =
  let open Answer in
  match (tau, tau') with
  | (Record _, _) | (_, Record _)
  | (Lam(_,_,_), _) | (_, Lam(_,_,_)) ->
      assert false (* only types that have the base kind are compared *)
  | (BVar _, _) | (_, BVar _) ->
      assert false
  | (BaseForall({ content = a ; _ } as a_loc, k,  t),
     BaseForall({ content = a' ; _ }, k', t'))
  | (BaseExists({ content = a ; _ } as a_loc, k', t),
     BaseExists({ content = a' ; _ }, k,  t')) ->
      sub_kind ~unfold_eq env k'.content k.content &*&
       (fun () ->
         let x = Var.bfresh a in
         let x_var = dummy_locate (mkVar x) in
         sub_type ~unfold_eq
           (Env.Typ.add_var (locate_with Mode.U a_loc) x k'.content env)
           (bsubst t a x_var) (bsubst t' a' x_var)
       )
  | (BaseArrow(t1,t2), BaseArrow(t1',t2')) ->
      sub_type ~unfold_eq env t1' t1 &*&
      (fun () -> sub_type ~unfold_eq env t2 t2')
  | (BaseRecord m, BaseRecord m') ->
      (* for every lab ∈ dom m', Γ ⊢ m(l) ≤ m'(l) must hold *)
      Label.Map.fold
        (fun lab tau' acc -> match acc with
        | Yes ->
            begin try
              let tau = Label.Map.find lab m in
              match sub_type ~unfold_eq env tau tau' with
              | Yes -> Yes
              | No reasons ->
                  No (TYPES_SUB
                        (dummy_locate
                           (mkBaseRecord (Label.Map.singleton lab tau)),
                         dummy_locate
                           (mkBaseRecord (Label.Map.singleton lab tau')))
                      :: reasons)
            with Not_found ->
              No [TYPES_MISSING_FIELD (lab, tau')]
            end
        | No reasons -> No reasons)
        m' Yes
  | (App(_,_), App(_,_)) | (Proj(_,_), Proj(_,_)) | (FVar _, FVar _) ->
      (* we already are in head normal form, so comparing
         for equivalence is enough *)
      Normalize.equiv_typ ~unfold_eq env
        (dummy_locate tau) (dummy_locate tau') Kind.mkBase
  | ((BaseForall (_,_,_) | BaseExists (_,_,_) | BaseArrow (_,_) |
    BaseRecord _ | App(_,_) | Proj(_,_) | FVar _),
     (BaseForall (_,_,_) | BaseExists (_,_,_) | BaseArrow (_,_) |
     BaseRecord _ | App(_,_) | Proj(_,_) | FVar _)) -> No []

and sub_type ~unfold_eq env tau tau' =
  let tau  = Normalize.head_norm ~unfold_eq env tau
  and tau' = Normalize.head_norm ~unfold_eq env tau' in
  let open Answer in
  match try_sub_type ~unfold_eq env tau.content tau'.content with
  | Yes -> Yes
  | No reasons -> No (TYPES_SUB (tau, tau') :: reasons)

let sub_type_b ~unfold_eq env k1 k2 =
  Answer.to_bool (sub_type ~unfold_eq env k1 k2)

let check_wftype env t k =
  Normalize.sub_kind ~unfold_eq:false env (wftype env t) k

let check_wftype_b env t k =
  Answer.to_bool (check_wftype env t k)
