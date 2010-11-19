open Ast
open Term
open Wftype
open Location
open Ast_utils

type basekind_res = OK | KIND of Typ.typ Typ.kind
let wfbasetype env t =
  let k = wftype env t in
  if sub_kind_b ~unfold_eq:false env k Kind.mkBase
  then OK
  else KIND k

let check_wftype env tau =
  try Wftype.check_wftype_b env tau Kind.mkBase
  with Error.ERROR _ -> false

let elim_typ_var_in_typ env y t =
  (* to try to eliminate y in t, we normalize t *)
  (* there is no general way to avoid y bu using subtyping *)
  (* here we just use type equivalence *)
  let t_norm = Normalize.typ_norm ~unfold_eq:false env t Kind.mkBase in
  if Typ.is_fv y t_norm
  then None
  else Some t_norm

let rec wfterm env term =
  Printf.eprintf "wfterm environment:\n%s%!"
    (Env.to_string env) ;
  match term.content with
  | BVar _ -> assert false
  | FVar x ->
      begin
        try
          let tau = Env.Term.get_var x env in
          assert (check_wftype env tau) ;
          (Env.clean_removed_vars env, tau)
            (* TODO: weakening *)
        with Not_found ->
          Error.raise_error Error.term_wf term.startpos term.endpos
            (Printf.sprintf "Unbound term variable: %s." (Var.to_string x))
        | Env.Removed_var loc ->
            Error.raise_error Error.term_wf term.startpos term.endpos
              (Printf.sprintf "The term variable %s cannot be used since the program point in %s."
                 (Var.to_string x) (location_msg loc))
      end
  | Lam ({ content = x ; _ } as x_loc, t, e) ->
      begin
        match wfbasetype env t with
        | OK ->
            let x' = Var.bfresh x in
            let x_var' = dummy_locate (mkVar x') in
            let (env', t') =
              wfterm
                (Env.Term.add_var x' (Location.relocate_with t x_loc) env)
                (bsubst_term_var e x x_var') in
            begin
              let open Answer in
              match Env.is_pure env' with
              | Yes ->
                  (Env.Term.remove_var ~track:false x' env',
                   dummy_locate (Typ.mkBaseArrow t t'))
              | No reason ->
                  Error.raise_error Error.purity e.startpos e.endpos
                    (Printf.sprintf
                       "This term is a body of a function and is not pure.\n%s%!"
                       (error_msg reason))
            end
        | KIND k ->
            Error.raise_error Error.term_wf t.startpos t.endpos
              (Printf.sprintf "This type should have kind ⋆, but has kind\n%s%!"
                 (PPrint.Kind.string k))
      end
  | App(e1, e2) ->
      begin
        let (env1, tau1) = wfterm env e1 in
        let tau1 = Normalize.head_norm ~unfold_eq:false env tau1 in
        (* necessary in case we have a path that is equivalent to an arrow *)
        match tau1.content with
        | Typ.BaseArrow(tau2', tau1') ->
            begin
              let (env2, tau2) = wfterm env e2 in
              let open Answer.WithValue in
              match Env.zip env1 env2 with
              | Yes env12 ->
                  begin
                    let open Answer in
                    match sub_type ~unfold_eq:false env tau2 tau2' with
                    | Yes -> (env12, tau1')
                    | No reason ->
                        Error.raise_error
                          Error.subtype term.startpos term.endpos
                          (Printf.sprintf "Ill-formed application\n%s%!"
                             (error_msg reason))
                  end
              | No reason ->
                  Error.raise_error Error.zip term.startpos term.endpos
                    (Printf.sprintf
                       "Ill-formed application because of inconsistent zip\n%s%!"
                       (error_msg reason))
            end
        | (Typ.BVar _ | Typ.FVar _ | Typ.BaseRecord _ |
          Typ.BaseForall (_, _, _) | Typ.BaseExists (_,_,_) |
          Typ.Proj (_, _) | Typ.Record _ |
          Typ.Lam (_, _, _) | Typ.App (_, _)) as tau ->
            Error.raise_error Error.term_wf e1.startpos e1.endpos
              (Printf.sprintf
                 "Non functional application: this term should have an arrow type,\nbut has type\n%s%!"
                 (PPrint.Typ.string (dummy_locate tau)))
      end
  | Let({ content = x ; _ } as x_loc, e1, e2) ->
      let (env1, t1) = wfterm env e1 in
      let y = Var.bfresh x in
      let y_var = dummy_locate (mkVar y) in
      let (env2, t2) =
        wfterm
          (Env.Term.add_var y (Location.relocate_with t1 x_loc) env)
          (bsubst_term_var e2 x y_var) in
      begin
        let open Answer.WithValue in
        match Env.zip env1 (Env.Term.remove_var ~track:false y env2) with
        | Yes env12 -> (env12, t2)
        | No reason ->
            Error.raise_error Error.zip term.startpos term.endpos
              (Printf.sprintf
                 "Ill-formed let binding because of inconsistent zip\n%s%!"
                 (error_msg reason))
      end
  | Gen ({ content = x ; _ } as x_loc, k, e) ->
      if wfkind env k.content
      then
        let x' = Typ.Var.bfresh x in
        let x_var' = locate_with (Typ.mkVar x') x_loc in
        let (env', t') =
          wfterm
            (Env.Typ.add_var (locate_with Mode.U x_loc) x' k.content env)
            (bsubst_typ_var e x x_var') in
        begin
          let open Answer in
          match Env.is_pure env' with
          | Yes ->
              assert (not (Env.Typ.is_fv x' env')) ;
              (Env.Typ.remove_var ~track:false ~recursive:false x' env',
               dummy_locate (Typ.mkBaseForall (locate_with x' x_loc) k t'))
          | No reason ->
              Error.raise_error Error.purity e.startpos e.endpos
                (Printf.sprintf
                   "This term is a body of a generalization and is not pure.\n%s%!"
                   (error_msg reason))
        end
      else
        Error.raise_error Error.kind_wf k.startpos k.endpos
          "Ill-formed kind at the bound of a generalization."
  | Inst(e, tau) ->
      begin
        let (env', t') = wfterm env e in
        let t' = Normalize.head_norm ~unfold_eq:false env t' in
        (* necessary in case we have a path that is equivalent to a ∀ *)
        match t'.content with
        | Typ.BaseForall({content = x ; _ }, k', tau') ->
            begin
              let k = wftype env tau in
              let open Answer in
              match sub_kind ~unfold_eq:false env k k'.content with
              | Yes -> (env', Typ.bsubst tau' x tau)
              | No reasons ->
                  Error.raise_error Error.subkind term.startpos term.endpos
                    (Printf.sprintf "Ill-formed instantiation:\n%s%!"
                       (error_msg reasons))
            end
        | (Typ.FVar _ | Typ.BVar _ | Typ.BaseArrow (_, _) |
          Typ.BaseExists (_,_,_) | Typ.BaseRecord _ | Typ.Proj (_, _) |
          Typ.Record _ | Typ.Lam (_, _, _) | Typ.App (_, _)) as tau' ->
            Error.raise_error Error.term_wf e.startpos e.endpos
              (Printf.sprintf
                 "Ill-formed instantiation: this term should have a universal type,\nbut has type\n%s%!"
                 (PPrint.Typ.string (dummy_locate tau')))
      end
  | Record r ->
      let (env', m) = Label.AList.fold
          (fun lab e (env_acc, m) ->
            let (env', tau) = wfterm env e in
            let open Answer.WithValue in
            match Env.zip env' env_acc with
            | Yes env_zip ->
                (env_zip, Label.Map.add lab tau m)
            | No reason ->
                Error.raise_error Error.zip term.startpos term.endpos
                  (Printf.sprintf
                     "Ill-formed record because of inconsistent zip\n%s%!"
                     (error_msg reason))
          )
          r (Env.empty, Label.Map.empty)
      in
      (env', dummy_locate (Typ.mkBaseRecord m))
  | Proj(e, lab) ->
      let (env', tau') = wfterm env e in
        let tau' = Normalize.head_norm ~unfold_eq:false env tau' in
        (* necessary in case we have a path that is equivalent to a record *)
      begin
        match tau'.content with
        | Typ.BaseRecord m ->
            begin
              try (env', Label.Map.find lab.content m)
              with Not_found ->
                Error.raise_error Error.term_wf lab.startpos lab.endpos
                  ("Unknown label " ^ lab.content ^ ".")
            end
        | (Typ.FVar _ | Typ.BVar _ | Typ.BaseArrow (_, _) |
          Typ.BaseForall (_, _, _) | Typ.BaseExists (_,_,_) |
          Typ.Proj (_, _) | Typ.Record _ |
          Typ.Lam (_, _, _) | Typ.App (_, _)) as tau ->
            Error.raise_error Error.term_wf e.startpos e.endpos
              (Printf.sprintf
                 "Ill-formed projection: this term should have a record type,\nbut has type\n%s%!"
                 (PPrint.Typ.string (dummy_locate tau)))
      end
  | Annot(e, t) ->
      begin
        let (env', t') = wfterm env e
        and k = wftype env t in
        let open Answer in
        match sub_kind ~unfold_eq:false env k Kind.mkBase with
        | Yes ->
            begin
              match sub_type ~unfold_eq:true env t' t with
              | Yes -> (env', t)
              | No reasons ->
                  Error.raise_error Error.subtype e.startpos e.endpos
                    (Printf.sprintf
                       "Ill-formed type annotation:\
 this term cannot be given the required type.\n%s%!"
       (error_msg reasons))
            end
        | No reasons ->
            Error.raise_error Error.subkind t.startpos t.endpos
              (Printf.sprintf
                 "Ill-formed type annotation:\
 this type should have a base kind.\n%s%!"
       (error_msg reasons))
      end
  | Sigma ({ content = Typ.FVar x ; _ } as x_loc,
           ({ content = y ; _ } as y_loc), k, t, e) ->
      let ({ content = mode ; _ }, k_x) =
        try Env.Typ.get_var x env
        with Not_found ->
          Error.raise_error Error.type_wf x_loc.startpos x_loc.endpos
            (Printf.sprintf "Unbound type variable: %s." (Typ.Var.to_string x))
        | Env.Removed_var loc ->
            Error.raise_error Error.term_wf term.startpos term.endpos
              (Printf.sprintf "The type variable %s cannot be used since the program point in %s."
                 (Typ.Var.to_string x) (location_msg loc))

      in begin
      (* checking mode *)
          match mode with
          | Mode.U -> (* normal case *)
              begin
                let open Answer in
                match (* check k_x ≡ k *)
                  Normalize.equiv_kind ~unfold_eq:false env k.content k_x
                with
                | Yes ->
                    let y' = Typ.Var.bfresh y in
                    let y_var' =  locate_with (Typ.mkVar y') y_loc in
                    let (env', t') =
                      let env = (* (env \ x) ∪ y :: k = t *)
                        Env.Typ.add_var
                          (locate_with (Mode.EQ t) y_loc) y' k.content
                          (Env.Typ.remove_var ~track:true ~recursive:true
                             x env) in
                      wfterm env (bsubst_typ_var e y y_var') in
                    assert (not (Env.Typ.is_fv y' env')) ;
                    assert (not (Env.Typ.is_fv x env')) ;
                    assert (not (Env.Typ.mem_var x env')) ;
                    (Env.Typ.add_var (locate_with Mode.E x_loc) x k_x
                       (Env.Typ.remove_var ~track:false ~recursive:false
                          y' env'), (* (env' \ y) ∪ ∃ x :: k_x *)
                     Typ.subst t' y' x_loc.content) (* t' [y' ← x] *)
                | No reason ->
                    Error.raise_error Error.subkind
                      x_loc.startpos x_loc.endpos
                      (Printf.sprintf "This kind of this type variable is not equivalent to the kind that is provided as argument to the Σ.\n%s%!"
                         (error_msg reason))
              end
          | Mode.E -> assert false
          | Mode.EQ _ ->
              Error.raise_error Error.misused_typ_var
                x_loc.startpos x_loc.endpos
                "This variable is equipped with an equation, hence it cannot be used by Σ."
      end
  | Sigma ({ content =
             (Typ.BVar _ | Typ.App _ | Typ.Lam _ | Typ.Record _ | Typ.Proj _ |
             Typ.BaseArrow _ | Typ.BaseRecord _ | Typ.BaseForall _ |
             Typ.BaseExists _) ; _ }, _, _, _, _) ->
               (* This case is not supported by the syntax *)
               assert false
  | Open ({ content = Typ.FVar x ; _ } as x_loc, e) ->
      let ({ content = mode ; _ }, k_x) =
        try Env.Typ.get_var x env
        with Not_found ->
          Error.raise_error Error.term_wf x_loc.startpos x_loc.endpos
            (Printf.sprintf "Unbound type variable: %s." (Typ.Var.to_string x))
        | Env.Removed_var loc ->
            Error.raise_error Error.type_wf term.startpos term.endpos
              (Printf.sprintf "The type variable %s cannot be used since the program point in %s."
                 (Typ.Var.to_string x) (location_msg loc))
      in
      begin
        (* checking mode *)
          match mode with
          | Mode.U -> (* normal case *)
              begin
                let (env', t') =
                  wfterm
                    (Env.Typ.remove_var ~track:true ~recursive:true x env) e in
                let t' = Normalize.head_norm ~unfold_eq:false env t' in
                (* necessary in case we have a path
                   that is equivalent to a ∃ *)
                match t'.content with
                | Typ.BaseExists({ content = y ; _ }, k, t') ->
                    begin
                      assert (not (Env.Typ.is_fv x env')) ;
                      assert (not (Env.Typ.mem_var x env')) ;
                      (* checking env ⊢ k ≡ k_x *)
                      let open Answer in
                      match 
                        Normalize.equiv_kind ~unfold_eq:false env k_x k.content
                      with
                      | Yes ->
                          (Env.Typ.add_var (locate_with Mode.E x_loc)
                             x k.content env',
                           Typ.bsubst t' y x_loc)
                      | No reason ->
                          Error.raise_error Error.subkind
                            x_loc.startpos x_loc.endpos
                            (Printf.sprintf "This kind of this type variable is not equivalent to the kind at the bound of the existential type of the argument.\n%s%!"
                               (error_msg reason))
                    end
                | (Typ.BVar _ | Typ.FVar _ | Typ.BaseRecord _ |
                  Typ.BaseForall (_, _, _) | Typ.BaseArrow (_,_) |
                  Typ.Proj (_, _) | Typ.Record _ |
                  Typ.Lam (_, _, _) | Typ.App (_, _)) ->
                    Error.raise_error Error.term_wf e.startpos e.endpos
                      (Printf.sprintf "Ill-formed opening: this term should have an existential type, but has type\n%s%!"
                         (Ast_utils.PPrint.Typ.string t'))
                    end
          | Mode.E -> assert false
          | Mode.EQ _ ->
              Error.raise_error Error.misused_typ_var
                x_loc.startpos x_loc.endpos
                "This variable is equipped with an equation, hence it cannot be used by open."
      end
  | Open ({ content =
            (Typ.BVar _ | Typ.App _ | Typ.Lam _ | Typ.Record _ | Typ.Proj _ |
            Typ.BaseArrow _ | Typ.BaseRecord _ | Typ.BaseForall _ |
            Typ.BaseExists _) ; _ }, _) ->
      (* this case is not supported by the syntax *)
      assert false
  | Nu ({ content = x ; _ } as x_loc, k, e) ->
      if wfkind env k.content
      then
        let x' = Typ.Var.bfresh x in
        let x_var' = locate_with (Typ.mkVar x') x_loc in
        let (env', t') =
          wfterm
            (Env.Typ.add_var (locate_with Mode.U x_loc) x' k.content env)
            (bsubst_typ_var e x x_var') in
        begin
          (* checking mode *)
          let mode =
            try (fst (Env.Typ.get_var x' env')).content
            with
            | Not_found -> assert false
            | Env.Removed_var loc ->
                Error.raise_error Error.type_wf term.startpos term.endpos
                  (Printf.sprintf "The type variable %s cannot be used since the program point in %s."
                     (Typ.Var.to_string x') (location_msg loc))
          in
          match mode with
          | Mode.U -> (* the variable was not used in an opening or a sigma *)
              Error.raise_error Error.misused_typ_var
                x_loc.startpos x_loc.endpos
                "This variable must be used as the argument of open or Σ."
          | Mode.E -> (* the variable was used in an opening or a sigma *)
              assert (not (Env.Typ.is_fv x' env')) ;
              if Typ.is_fv x' t'
              then begin
                assert (Env.Typ.mem_var x' env') ;
                assert(check_wftype env' t') ;
                match elim_typ_var_in_typ env' x' t' with
                | Some t' ->
                    (Env.Typ.remove_var ~track:false ~recursive:false x' env',
                     t')
                | None ->
                    Error.raise_error Error.escaping_typ_var
                      x_loc.startpos x_loc.endpos
                      (Printf.sprintf
                         "Cannot eliminate this type variable from the type of the body:\n%s%!"
                         (Ast_utils.PPrint.Typ.string t'))
              end
              else
                (Env.Typ.remove_var ~track:false ~recursive:false x' env', t')
          | Mode.EQ _ -> assert false
        end
      else
        Error.raise_error Error.kind_wf k.startpos k.endpos
          "Ill-formed kind at the bound of a type variable restriction."
  | Ex ({ content = x ; _ } as x_loc, k, e) ->
      if wfkind env k.content
      then
        let x' = Typ.Var.bfresh x in
        let x_var' = locate_with (Typ.mkVar x') x_loc in
        let (env', t') =
          wfterm
            (Env.Typ.add_var (locate_with Mode.U x_loc) x' k.content env)
            (bsubst_typ_var e x x_var') in
        begin
          let mode =
            try (fst (Env.Typ.get_var x' env')).content
            with
            | Not_found -> assert false
            | Env.Removed_var loc ->
                Error.raise_error Error.type_wf term.startpos term.endpos
                  (Printf.sprintf "The type variable %s cannot be used since the program point in %s."
                     (Typ.Var.to_string x') (location_msg loc))
          in
          match mode with
          | Mode.U -> (* the variable was not used in an opening or a sigma *)
              Error.raise_error Error.misused_typ_var
                x_loc.startpos x_loc.endpos
                "This variable must be used as the argument of open or Σ."
          | Mode.E -> (* the variable was used in an opening or a sigma *)
              assert (not (Env.Typ.is_fv x' env')) ;
              (Env.Typ.remove_var ~track:false ~recursive:false x' env',
               dummy_locate (Typ.mkBaseExists (locate_with x' x_loc) k t'))
          | Mode.EQ _ -> assert false
        end
      else
        Error.raise_error Error.kind_wf k.startpos k.endpos
          "Ill-formed kind at the bound of an existential closure."

let check_wfterm env e t =
  let (_, t_min) = wfterm env e in
  sub_type_b ~unfold_eq:false env t_min t
