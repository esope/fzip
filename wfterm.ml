open Ast
open Term
open Wftype
open Location
open Ast_utils

let rec is_extended_result e = match e.content with
| FVar _ | BVar _ -> true
| Proj(e, _) | Annot(e, _) -> is_extended_result e
| Record m ->
    Label.AList.for_all
      (fun _lab (_x, e) -> is_extended_result e)
      m
| App(_,_) | Inst(_,_) | Open(_,_) -> false
| Fix({ content = x ; _ }, _, e) ->
    let x' = Var.bfresh x in
    let x_var' = dummy_locate (mkVar x') in
    is_extended_result (bsubst_term_var e x x_var')
| Sigma(_,{ content = x ; _ },_,_,e)
| Nu({content = x ; _ }, _ , e) ->
    let x' = Typ.Var.bfresh x in
    let x_var' = dummy_locate (Typ.mkVar x') in
    is_extended_result (bsubst_typ_var e x x_var')
| Gen _ | Lam _ | Ex _ -> is_result e

and is_result e = match e.content with
| Annot(e, _) -> is_result e
| Sigma(_,{ content = x ; _ },_,_,e) ->
    let x' = Typ.Var.bfresh x in
    let x_var' = dummy_locate (Typ.mkVar x') in
    is_result (bsubst_typ_var e x x_var')
| Open _ | Fix _ | Inst _ | Proj _ | Nu _ | Ex _ | Gen _ | Record _ |
  Lam _ | App _ | BVar _ | FVar _ -> is_value e

and is_value t = match t.content with
| Gen(_,_,_) | Lam(_,_,_) -> true
| Annot(e, _) -> is_value e
| Record m ->
    Label.AList.for_all
      (fun _lab (_x, e) -> is_value e)
      m
| Ex({ content = x ; _ }, _,
     { content = Sigma({ content = Typ.BVar x' ; _ }, y, _, _, e) ; _ })
  when Typ.Var.bequal x x' ->
    let y' = Typ.Var.bfresh y.content in
    let y_var' = dummy_locate (Typ.mkVar y') in
    is_value (bsubst_typ_var e y.content y_var')
| App _ | FVar _ | BVar _ | Inst _ | Proj _ | Fix _ |
  Open _ | Nu _ | Sigma _
| Ex(_,_,
     { content =
       Sigma({ content = (Typ.FVar _  | Typ.BaseArrow (_, _) |
       Typ.BaseRecord _ | Typ.BaseExists (_, _, _) | Typ.BaseForall (_, _, _) |
       Typ.Proj (_, _) | Typ.Record _ | Typ.Lam (_, _, _) |
       Typ.App (_, _) | Typ.BVar _); _ },_,_,_,_) ; _ })
| Ex
  (_, _,
  { content =
    (Open (_, _)|Nu (_, _, _)|Ex (_, _, _)|Annot (_, _)|Fix (_, _, _)|
    Inst (_, _)|Gen (_, _, _)|Proj (_, _)|Record _|
    Lam (_, _, _)|App (_, _)|BVar _|FVar _) ; _ }) -> false

let rec check_fixpoint_syntax e = match e.content with
| FVar _ | BVar _ -> true
| Sigma (_, x, _, _, e) | Nu (x, _, e) | Ex (x, _, e) | Gen (x, _, e) ->
    let x' = Typ.Var.bfresh x.content in
    let x_var' = dummy_locate (Typ.mkVar x') in
    check_fixpoint_syntax (bsubst_typ_var e x.content x_var')
| Annot (e, _) | Inst (e, _) | Proj (e, _) | Open (_, e) ->
    check_fixpoint_syntax e
| Fix (x, _, e) ->
    let x' = Var.bfresh x.content in
    let x_var' = dummy_locate (mkVar x') in
    let e' = bsubst_term_var e x.content x_var' in
    is_extended_result e' && check_fixpoint_syntax e'
| Record m ->
    Label.AList.for_all (fun _lab (_x, e) -> check_fixpoint_syntax e) m
| Lam (x, _, e) ->
    let x' = Var.bfresh x.content in
    let x_var' = dummy_locate (mkVar x') in
    check_fixpoint_syntax (bsubst_term_var e x.content x_var')
| App (e1, e2) ->
    check_fixpoint_syntax e1 && check_fixpoint_syntax e2

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
  match term.content with
  | BVar _ -> assert false
  | FVar x ->
      begin
        try
          let tau = Env.Term.get_var x env in
          assert (check_wftype env tau) ;
          let min_env = (* minimal typing environment *)
            Env.Term.add_var x tau
              (Env.Typ.minimal_env_for_vars env (Ast.Typ.fv tau)) in
          (min_env, tau)
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
              match Env.is_pure env' with
              | Answer.Yes ->
                  let env =
                    let min_env_for_t =
                      Env.Typ.minimal_env_for_vars env (Ast.Typ.fv t)
                    and min_env_for_e =
                      Env.Term.remove_var ~track:false
                        x' (Location.locate_with () x_loc) env'
                    in match Env.zip min_env_for_e min_env_for_t with
                    | Answer.WithValue.Yes env -> env
                    | Answer.WithValue.No _ -> assert false
                  in
                  (env,
                   dummy_locate (Typ.mkBaseArrow t t'))
              | Answer.No reason ->
                  Error.raise_error Error.purity e.startpos e.endpos
                    (Printf.sprintf
                       "This term is a body of a function and is not pure.\n%s%!"
                       (Answer.error_msg reason))
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
              let env =
                let min_env_for_k =
                  Env.Typ.minimal_env_for_vars env (Ast.Kind.fv k.content)
                and min_env_for_e =
                  assert (not (Env.Typ.is_fv x' env')) ;
                  Env.Typ.remove_var ~track:false ~recursive:false
                    x' (Location.locate_with () x_loc) env'
                in match Env.zip min_env_for_e min_env_for_k with
                | WithValue.Yes env -> env
                | WithValue.No _ -> assert false
              in
              (env,
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
              | Yes ->
                  let env =
                    let min_env_for_tau =
                      Env.Typ.minimal_env_for_vars env (Ast.Typ.fv tau)
                    in match Env.zip env' min_env_for_tau with
                    | WithValue.Yes env -> env
                    | WithValue.No _ -> assert false
                  in
                  (env, Typ.bsubst tau' x tau)
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
      (* let (env', m) = Label.AList.fold *)
      (*     (fun lab (x, e) (env_acc, m) -> (\* TODO: use x !!! *\) *)
      (*       let (env', tau) = wfterm env e in *)
      (*       let open Answer.WithValue in *)
      (*       match Env.zip env' env_acc with *)
      (*       | Yes env_zip -> *)
      (*           (env_zip, Label.Map.add lab tau m) *)
      (*       | No reason -> *)
      (*           Error.raise_error Error.zip term.startpos term.endpos *)
      (*             (Printf.sprintf *)
      (*                "Ill-formed record because of inconsistent zip\n%s%!" *)
      (*                (error_msg reason)) *)
      (*     ) *)
      (*     r (Env.empty, Label.Map.empty) *)
      (* in *)
    let (env', m) = wfterm_fields term.endpos env r in
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
              | Yes ->
                  let env =
                    let min_env_for_t =
                      Env.Typ.minimal_env_for_vars env (Ast.Typ.fv t)
                    in match Env.zip env' min_env_for_t with
                    | WithValue.Yes env -> env
                    | WithValue.No _ -> assert false
                  in (env, t)
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
                     let env_minus_x =
                       Env.Typ.remove_var ~track:true ~recursive:true
                         x (Location.locate_with () x_loc) env in
                     if wfkind env_minus_x k.content
                     then (* k is well_formed *)
                       let open Answer in
                       match (* check k_x ≡ k *)
                         Normalize.equiv_kind ~unfold_eq:false env k.content k_x
                       with
                       | Yes ->
                           begin
                             (* checking that e \ x ⊢ t :: k *)
                             match Wftype.check_wftype env_minus_x t k.content
                             with
                             | Yes ->
                                 let y' = Typ.Var.bfresh y in
                                 let y_var' =
                                   locate_with (Typ.mkVar y') y_loc in
                                 let (env', t') =
                                   let env = (* (env \ x) ∪ y :: k = t *)
                                     Env.Typ.add_var
                                       (locate_with (Mode.EQ t) y_loc)
                                       y' k.content env_minus_x in
                                   wfterm env (bsubst_typ_var e y y_var') in
                                 assert (not (Env.Typ.is_fv y' env')) ;
                                 assert (not (Env.Typ.is_fv x env')) ;
                                 assert (not (Env.Typ.mem_var x env')) ;
                                 let env =
                                   let min_env_for_t_k =
                                     Env.Typ.minimal_env_for_vars env_minus_x
                                       (Ast.Typ.Var.Set.union
                                          (Ast.Typ.fv t)
                                          (Ast.Kind.fv k.content)) in
                                   let min_env_for_e =
                                     (* (env' \ y) ∪ ∃ x :: k_x *)
                                     Env.Typ.add_var
                                       (locate_with Mode.E x_loc) x k_x
                                       (Env.Typ.remove_var
                                          ~track:false ~recursive:false
                                          y' (Location.locate_with () y_loc)
                                          env')
                                   in
                                   match Env.zip min_env_for_e min_env_for_t_k
                                   with
                                   | WithValue.Yes env -> env
                                   | WithValue.No _ -> assert false
                                 in
                                 (env,
                                  Typ.subst t' y' x_loc.content)
                                   (* t' [y' ← x] *)
                             | No reasons ->
                                 Error.raise_error Error.type_wf
                                   t.startpos t.endpos
                                   (Printf.sprintf
                                      "This type has not the required kind.\n%s"
                                      (error_msg reasons))
                           end
                       | No reason ->
                           Error.raise_error Error.subkind
                             x_loc.startpos x_loc.endpos
                             (Printf.sprintf "This kind of this type variable is not equivalent to the kind that is provided as argument to the Σ.\n%s%!"
                                (error_msg reason))
                     else (* k is not wellformed *)
                       Error.raise_error Error.kind_wf k.startpos k.endpos
                         "Ill-formed kind in the definition part of a Σ."
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
                  (Env.Typ.remove_var ~track:true ~recursive:true
                     x (Location.locate_with () x_loc) env) e in
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
                    let env =
                      let min_env_for_k =
                        Env.Typ.minimal_env_for_vars env (Ast.Kind.fv k.content)
                      and min_env_for_e =
                        Env.Typ.remove_var ~track:false ~recursive:false
                          x' (Location.locate_with () x_loc) env'
                      in match Env.zip min_env_for_e min_env_for_k with
                      | Answer.WithValue.Yes env -> env
                      | Answer.WithValue.No _ -> assert false 
                    in
                    (env, t')
                | None ->
                    Error.raise_error Error.escaping_typ_var
                      x_loc.startpos x_loc.endpos
                      (Printf.sprintf
                         "Cannot eliminate this type variable from the type of the body:\n%s%!"
                         (Ast_utils.PPrint.Typ.string t'))
              end
              else
                (Env.Typ.remove_var ~track:false ~recursive:false
                   x' (Location.locate_with () x_loc) env', t')
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
              let env =
                let min_env_for_k =
                  Env.Typ.minimal_env_for_vars env (Ast.Kind.fv k.content)
                and min_env_for_e =
                  Env.Typ.remove_var ~track:false ~recursive:false
                    x' (Location.locate_with () x_loc) env'
                in match Env.zip min_env_for_e min_env_for_k with
                | Answer.WithValue.Yes env -> env
                | Answer.WithValue.No _ -> assert false 
              in
              (env,
               dummy_locate (Typ.mkBaseExists (locate_with x' x_loc) k t'))
          | Mode.EQ _ -> assert false
        end
      else
        Error.raise_error Error.kind_wf k.startpos k.endpos
          "Ill-formed kind at the bound of an existential closure."
  | Fix ({ content = x ; _ } as x_loc, t, e) ->
      match wfbasetype env t with
      | OK ->
          begin
            let x' = Var.bfresh x in
            let x_var' = locate_with (mkVar x') x_loc in
            let (env', t') =
              wfterm
                (Env.Term.add_var x' (Location.relocate_with t x_loc) env)
                (bsubst_term_var e x x_var') in
            let open Answer in
            match Wftype.sub_type ~unfold_eq:false env t' t with
            | Answer.Yes ->
                let env =
                  let min_env_for_t =
                    Env.Typ.minimal_env_for_vars env (Ast.Typ.fv t)
                  and min_env_for_e =
                    Env.Term.remove_var ~track:false
                      x' (Location.locate_with () x_loc) env'
                  in match Env.zip min_env_for_e min_env_for_t with
                  | WithValue.Yes env -> env
                  | WithValue.No _ -> assert false
                in
                (env, t)
            | Answer.No reasons ->
                Error.raise_error Error.subtype term.startpos term.endpos
                  (Printf.sprintf
                     "Ill-formed fixpoint:\
                     this term cannot be given the required type.\n%s%!"
                           (error_msg reasons))
          end
      | KIND k ->
          Error.raise_error Error.term_wf t.startpos t.endpos
            (Printf.sprintf "This type should have kind ⋆, but has kind\n%s%!"
               (PPrint.Kind.string k))

and wfterm_fields endpos env = function
| [] -> (Env.empty, Label.Map.empty)
| (lab, ({ content = x; _ } as x_loc, e)) :: f ->
    let (env', tau) = wfterm env e in
    let x' = Var.bfresh x in
    let x_var' = locate_with (mkVar x') x_loc in
    let (env'', m) =
      wfterm_fields endpos
        (Env.Term.add_var x' (Location.relocate_with tau x_loc) env)
        (bsubst_term_fields f x x_var') in
    let open Answer.WithValue in
    let env'' =
      Env.Term.remove_var ~track:false
        x' (Location.locate_with () x_loc) env'' in
    match Env.zip env' env'' with
    | Yes env_zip ->
      (env_zip, Label.Map.add lab tau m)
    | No reason ->
      Error.raise_error Error.zip x_loc.startpos endpos
        (Printf.sprintf
           "Ill-formed record because of inconsistent zip\n%s%!"
           (error_msg reason))

let wfterm env e =
  if check_fixpoint_syntax e
  then wfterm env e
  else
    Error.raise_error Error.term_wf e.startpos e.endpos
      "Ill-formed fixpoint: this term should be an extended result."
      

let check_wfterm env e t =
  let (_, t_min) = wfterm env e in
  sub_type_b ~unfold_eq:false env t_min t
