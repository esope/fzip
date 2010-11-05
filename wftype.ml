open Ast.Typ
open Ast_utils
open Location

type env = (typ, typ kind) Env.t

let rec single_ext k t = match k with
| Base -> Single t
| Single _u as k -> k
| Pi(y, k1, k2) ->
    let x = Var.bfresh y in
    let x_var = dummy_locate (FVar x) in
    let k2' =
      single_ext (bsubst_kind k2 y x_var) (dummy_locate (App(t, x_var))) in
    mkPi x k1 k2'
| Sigma(y, k1, k2) ->
    let t1 = dummy_locate (Proj(t, dummy_locate "fst")) in
    let k1' = single_ext k1 t1
    and k2' = single_ext (bsubst_kind k2 y t1)
        (dummy_locate (Proj(t, dummy_locate "snd"))) in
    mkProd k1' k2'

let rec wfsubkind env k1 k2 =
  let open Answer in
  match (k1, k2) with
  | (Base, Base) | (Single _, Base) -> Yes
  | (Pi(x,k1, k2), Pi(x',k1', k2')) ->
      wfsubkind env k1' k1 &*&
      let y = Var.bfresh x in
      let y_var = dummy_locate (FVar y) in
      wfsubkind (Env.add_typ_var y k1' env)
        (bsubst_kind k2 x y_var) (bsubst_kind k2' x' y_var)
  | (Sigma(x,k1, k2), Sigma(x',_k1', k2')) ->
      wfsubkind env k1 k1 &*&
      let y = Var.bfresh x in
      let y_var = dummy_locate (FVar y) in
      wfsubkind (Env.add_typ_var y k1 env)
        (bsubst_kind k2 x y_var) (bsubst_kind k2' x' y_var)
  | (Single t, Single t') ->
      Normalize.equiv_typ env t t' Base
  | ((Base | Single _ | Pi(_,_,_) | Sigma(_,_,_)), _) -> No [ KINDS (k1,k2) ]

let wfsubkind_b env k1 k2 = Answer.to_bool (wfsubkind env k1 k2)

let rec wftype env t =
  let open Answer in
  match t.content with
  | BVar _ -> assert false
  | FVar x -> single_ext (Env.get_typ_var x env) t
  | App(t1, t2) ->
      let k1 = wftype env t1 and k2 = wftype env t2 in 
      begin
        match k1 with
        | Pi(x, k2', k1') ->
            begin
              match wfsubkind env k2 k2' with
              | Yes -> bsubst_kind k1' x t2
              | No reasons ->
                  Error.raise_error Error.type_wf t.startpos t.endpos
                    (Printf.sprintf "Ill-kinded application:\n%s%!"
                       (error_msg reasons))
            end
        | Base | Single _ | Sigma (_,_,_) ->
            Error.raise_error Error.type_wf t.startpos t.endpos
              "Non functional application."
      end
  | Lam(x, k, t) ->
      if wfkind env k.content
      then
        let x' = Var.bfresh x in
        let t' = bsubst_typ t x (dummy_locate (FVar x')) in
        let k' = wftype (Env.add_typ_var x' k.content env) t' in
        mkPi x' k.content k'
      else
        Error.raise_error Error.kind_wf k.startpos k.endpos "Ill-formed kind."
  | Pair(k1, k2) ->
      let k1 = wftype env k1 
      and k2 = wftype env k2 in
      mkProd k1 k2
  | Proj(t', lab) ->
      let k = wftype env t' in
      begin
        match k with
        | Sigma(_, k1, _) when lab.content = "fst" -> k1
        | Sigma(x, _, k2) when lab.content = "snd" ->
            bsubst_kind k2 x (dummy_locate (Proj(t', dummy_locate "fst")))
        | Sigma(_, _, _) ->
            Error.raise_error Error.type_wf t.startpos t.endpos
              (Printf.sprintf
                 "Ill-formed projection: unknown label %s." lab.content)
        | Base | Single _ | Pi(_,_,_) ->
            Error.raise_error Error.type_wf t.startpos t.endpos
              "Ill-formed projection."
      end
  | BaseForall(x, k, u) ->
      if wfkind env k.content
      then
        let x' = Var.bfresh x in
        let u' = bsubst_typ u x (dummy_locate (FVar x')) in
        let env' = Env.add_typ_var x' k.content env in
        let k' = wftype env' u' in
        if wfsubkind_b env' k' Base 
        then Single t
        else Error.raise_error Error.type_wf k.startpos k.endpos
            "Ill-formed universal type: this kind is not a base kind."
      else Error.raise_error Error.kind_wf k.startpos k.endpos
          "Ill-formed kind."
  | BaseArrow(t1, t2) ->
      begin
        if wfsubkind_b env (wftype env t1) Base
        then if wfsubkind_b env (wftype env t2) Base
        then Single t
        else Error.raise_error Error.type_wf t2.startpos t2.endpos
            "Ill-formed basic product type: this type has not a base kind."
        else Error.raise_error Error.type_wf t1.startpos t1.endpos
            "Ill-formed basic product type: this type has not a base kind."
      end
  | BaseRecord m ->
      Label.Map.iter (fun _lab t -> ignore (wftype env t)) m ;
      Single t

and wfkind env = function
  | Base -> true
  | Pi(y, k1, k2) | Sigma(y, k1, k2) ->
      wfkind env k1 &&
      let x = Var.bfresh y in
      let x_var = dummy_locate (FVar x) in
      wfkind (Env.add_typ_var x k1 env) (bsubst_kind k2 y x_var)
  | Single t ->
      match wftype env t with
      | Single _ | Base -> true
      | Pi(_,_,_) | Sigma(_,_,_) ->
          Error.raise_error Error.kind_wf t.startpos t.endpos
            "Ill-formed singleton: this type has not a base kind."

let rec try_wfsubtype env tau tau' =
  let open Answer in
  match (tau, tau') with
  | (Pair(_, _), _) | (_, Pair(_, _))
  | (Lam(_,_,_), _) | (_, Lam(_,_,_)) ->
      assert false (* only types that have the base kind are compared *)
  | (BVar _, _) | (_, BVar _) ->
      assert false
  | (BaseForall(a, k,t), BaseForall(a', k',t')) ->
      wfsubkind env k'.content k.content &*&
      let x = Var.bfresh a in
      let x_var = dummy_locate (FVar x) in
      wfsubtype (Env.add_typ_var x k'.content env)
        (bsubst_typ t a x_var) (bsubst_typ t' a' x_var)
  | (BaseArrow(t1,t2), BaseArrow(t1',t2')) ->
      wfsubtype env t1' t1 &*& wfsubtype env t2 t2'
  | (BaseRecord m, BaseRecord m') ->
      (* for every lab ∈ dom m', Γ ⊢ m(l) ≤ m'(l) must hold *)
      Label.Map.fold
        (fun lab tau' acc -> match acc with
        | Yes ->
            begin try
              let tau = Label.Map.find lab m in
              wfsubtype env tau tau'
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
  | ((BaseForall (_,_,_) | BaseArrow (_,_) | BaseRecord _ |
    App(_,_) | Proj(_,_) | FVar _),
     (BaseForall (_,_,_) | BaseArrow (_,_) | BaseRecord _ |
     App(_,_) | Proj(_,_) | FVar _)) -> No []

and wfsubtype env tau tau' =
  let (tau,  _) = Normalize.head_norm env tau
  and (tau', _) = Normalize.head_norm env tau' in
  let open Answer in
  match try_wfsubtype env tau.content tau'.content with
  | Yes -> Yes
  | No reasons -> No (TYPES (tau, tau') :: reasons)

let wfsubtype_b env k1 k2 = Answer.to_bool (wfsubtype env k1 k2)
