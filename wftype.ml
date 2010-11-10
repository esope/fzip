open Ast
open Ast.Typ
open Ast_utils
open Location

type env = (typ, typ kind) Env.t

let sub_kind = Normalize.sub_kind
let sub_kind_b = Normalize.sub_kind_b

let rec wftype env t =
  let open Answer in
  match t.content with
  | BVar _ -> assert false
  | FVar x ->
      begin
        try Single (t, Env.Typ.get_var x env)
        with Not_found ->
          Error.raise_error Error.type_wf t.startpos t.endpos
            (Printf.sprintf "Unbound type variable: %s." (Var.to_string x))
      end
  | App(t1, t2) ->
      let k1 = wftype env t1 and k2 = wftype env t2 in 
      begin
        match Normalize.simplify_kind k1 with
        | Pi(x, k2', k1') ->
            begin
              match sub_kind env k2 k2' with
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
  | Lam(x, k, t) ->
      if wfkind env k.content
      then
        let x' = Var.bfresh x in
        let t' = bsubst t x (dummy_locate (FVar x')) in
        let k' = wftype (Env.Typ.add_var x' k.content env) t' in
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
  | BaseForall(x, k, u) | BaseExists(x, k, u) ->
      if wfkind env k.content
      then
        let x' = Var.bfresh x in
        let u' = bsubst u x (dummy_locate (FVar x')) in
        let env' = Env.Typ.add_var x' k.content env in
        let k' = wftype env' u' in
        if sub_kind_b env' k' Base 
        then Single (t, Base)
        else Error.raise_error Error.type_wf k.startpos k.endpos
            "Ill-formed universal type: this kind is not a base kind."
      else Error.raise_error Error.kind_wf k.startpos k.endpos
          "Ill-formed kind."
  | BaseArrow(t1, t2) ->
      begin
        if sub_kind_b env (wftype env t1) Base
        then if sub_kind_b env (wftype env t2) Base
        then Single (t, Base)
        else Error.raise_error Error.type_wf t2.startpos t2.endpos
            "Ill-formed basic product type: this type has not a base kind."
        else Error.raise_error Error.type_wf t1.startpos t1.endpos
            "Ill-formed basic product type: this type has not a base kind."
      end
  | BaseRecord m ->
      Label.Map.iter (fun _lab t -> ignore (wftype env t)) m ;
      Single (t, Base)

and wfkind env = function
  | Base -> true
  | Sigma f -> wfkind_fields env f
  | Pi(y, k1, k2) ->
      wfkind env k1 &&
      let x = Var.bfresh y in
      let x_var = dummy_locate (FVar x) in
      wfkind (Env.Typ.add_var x k1 env) (Kind.bsubst k2 y x_var)
  | Single (t, k) ->
      let k' = wftype env t in
      let open Answer in
      match sub_kind env k' k with
      | Yes -> true
      | No reasons ->
          Error.raise_error Error.kind_wf t.startpos t.endpos
            (Printf.sprintf "Ill-formed singleton:\n%s%!"
               (error_msg (WF_TYPE (t, k) :: reasons)))

and wfkind_fields env = function
  | [] -> true
  | (_lab, (x, k)) :: f ->
      wfkind env k &&
      let y = Var.bfresh x in
      let y_var = dummy_locate (FVar y) in
      wfkind_fields (Env.Typ.add_var y k env) (Kind.bsubst_fields f x y_var)

let rec try_sub_type env tau tau' =
  let open Answer in
  match (tau, tau') with
  | (Record _, _) | (_, Record _)
  | (Lam(_,_,_), _) | (_, Lam(_,_,_)) ->
      assert false (* only types that have the base kind are compared *)
  | (BVar _, _) | (_, BVar _) ->
      assert false
  | (BaseForall(a, k,  t), BaseForall(a', k', t'))
  | (BaseExists(a, k', t), BaseExists(a', k,  t')) ->
      sub_kind env k'.content k.content &*&
      let x = Var.bfresh a in
      let x_var = dummy_locate (FVar x) in
      sub_type (Env.Typ.add_var x k'.content env)
        (bsubst t a x_var) (bsubst t' a' x_var)
  | (BaseArrow(t1,t2), BaseArrow(t1',t2')) ->
      sub_type env t1' t1 &*& sub_type env t2 t2'
  | (BaseRecord m, BaseRecord m') ->
      (* for every lab ∈ dom m', Γ ⊢ m(l) ≤ m'(l) must hold *)
      Label.Map.fold
        (fun lab tau' acc -> match acc with
        | Yes ->
            begin try
              let tau = Label.Map.find lab m in
              sub_type env tau tau'
            with Not_found ->
              No [TYPES
                    (dummy_locate (BaseRecord Label.Map.empty),
                     dummy_locate (BaseRecord (Label.Map.singleton lab tau')))]
            end
        | No reasons -> No reasons)
        m' Yes
  | (App(_,_), App(_,_)) | (Proj(_,_), Proj(_,_)) | (FVar _, FVar _) ->
      (* we already are in head normal form, so comparing
         for equivalence is enough *)
      Normalize.equiv_typ env (dummy_locate tau) (dummy_locate tau') Base
  | ((BaseForall (_,_,_) | BaseExists (_,_,_) | BaseArrow (_,_) |
    BaseRecord _ | App(_,_) | Proj(_,_) | FVar _),
     (BaseForall (_,_,_) | BaseExists (_,_,_) | BaseArrow (_,_) |
     BaseRecord _ | App(_,_) | Proj(_,_) | FVar _)) -> No []

and sub_type env tau tau' =
  let (tau,  _) = Normalize.head_norm env tau
  and (tau', _) = Normalize.head_norm env tau' in
  let open Answer in
  match try_sub_type env tau.content tau'.content with
  | Yes -> Yes
  | No reasons -> No (TYPES (tau, tau') :: reasons)

let sub_type_b env k1 k2 = Answer.to_bool (sub_type env k1 k2)

let check_wftype env t k = Normalize.sub_kind_b env (wftype env t) k
