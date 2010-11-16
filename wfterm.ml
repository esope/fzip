open Ast
open Term
open Wftype
open Location
open Ast_utils

type env = (Typ.typ, Typ.typ Typ.kind) Env.t

type basekind_res = OK | KIND of Typ.typ Typ.kind
let wfbasetype env t =
  let k = wftype env t in
  if sub_kind_b env k Kind.mkBase
  then OK
  else KIND k

let rec wfterm env term = match term.content with
  | BVar _ -> assert false
  | FVar x ->
      begin
        try Env.Term.get_var x env
        with Not_found ->
          Error.raise_error Error.term_wf term.startpos term.endpos
            (Printf.sprintf "Unbound term variable: %s." (Var.to_string x))
      end
  | Lam ({ content = x ; _ }, t, e) ->
      begin
        match wfbasetype env t with
        | OK ->
            let x' = Var.bfresh x in
            let x_var' = dummy_locate (mkVar x') in
            let t' =
              wfterm (Env.Term.add_var x' t env) (bsubst_term_var e x x_var') in
            dummy_locate (Typ.mkBaseArrow t t')
        | KIND k ->
            Error.raise_error Error.term_wf t.startpos t.endpos
              (Printf.sprintf "This type should have kind ⋆, but has kind\n%s%!"
                 (PPrint.Kind.string k))
      end
  | App(e1, e2) ->
      begin
        match (wfterm env e1).content with
        | Typ.BaseArrow(tau2', tau1') ->
            begin
              let tau2 = wfterm env e2 in
              let open Answer in
              match sub_type env tau2 tau2' with
              | Yes -> tau1'
              | No reason ->
                  Error.raise_error Error.subtype e1.startpos e2.endpos
                    (Printf.sprintf "Ill-formed application\n%s%!"
                       (error_msg reason))
            end
        | (Typ.BVar _ | Typ.FVar _ | Typ.BaseRecord _ |
          Typ.BaseForall (_, _, _) | Typ.BaseExists (_,_,_) |
          Typ.Proj (_, _) | Typ.Record _ |
          Typ.Lam (_, _, _) | Typ.App (_, _)) as tau ->
            Error.raise_error Error.term_wf e1.startpos e2.startpos
              (Printf.sprintf
                 "Non functional application: this term should have an arrow type,\nbut has type\n%s%!"
                 (PPrint.Typ.string (dummy_locate tau)))
      end
  | Let({ content = x ; _ }, e1, e2) ->
      let t1 = wfterm env e1 in
      let y = Var.bfresh x in
      let y_var = dummy_locate (mkVar y) in
      wfterm (Env.Term.add_var y t1 env) (bsubst_term_var e2 x y_var)
  | Gen ({ content = x ; _ } as x_loc, k, e) ->
      if wfkind env k.content
      then
        let x' = Typ.Var.bfresh x in
        let x_var' = locate_with (Typ.mkVar x') x_loc in
        let t' =
          wfterm
            (Env.Typ.add_var (locate_with Env.Typ.U x_loc) x' k.content env)
            (bsubst_typ_var e x x_var') in
        dummy_locate (Typ.mkBaseForall (locate_with x' x_loc) k t')
      else
        Error.raise_error Error.kind_wf k.startpos k.endpos
          "Ill-formed kind at the bound of a generalization."
  | Inst(e, tau) ->
      begin
        match (wfterm env e).content with
        | Typ.BaseForall({content = x ; _ }, k', tau') ->
            begin
              let k = wftype env tau in
              let open Answer in
              match sub_kind env k k'.content with
              | Yes -> Typ.bsubst tau' x tau
              | No reasons ->
                  Error.raise_error Error.subkind e.startpos tau.endpos
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
      let m = Label.AList.fold
          (fun lab e acc ->
            Label.Map.add lab (wfterm env e) acc)
          r Label.Map.empty
      in
      dummy_locate (Typ.mkBaseRecord m)
  | Proj(e, lab) ->
      begin
        match (wfterm env e).content with
        | Typ.BaseRecord m ->
            begin
              try Label.Map.find lab.content m
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
        let t' = wfterm env e
        and k = wftype env t in
        let open Answer in
        match sub_kind env k Kind.mkBase with
        | Yes ->
            begin
              match sub_type env t' t with
              | Yes -> t
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
  | Sigma (_,_,_,_,_)
  | Open (_,_)
  | Nu (_,_,_)
  | Ex (_,_,_) ->
      Error.raise_error Error.not_implemented term.startpos term.endpos
        "Typechecking for open existential types."

let check_wfterm env e t =
  let t_min = wfterm env e in
  sub_type_b env t_min t
