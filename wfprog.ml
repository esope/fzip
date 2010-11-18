type t = Ast.Prog.t
type reqs = Ast.Prog.reqs

open Location
open Ast
open Prog

(* returns (env, dom_te, dom_ty, exist_vars) *)
let rec wfreqs = let open Answer.WithValue in function
  | [] ->
      (Env.empty, Term.Var.Set.empty, Typ.Var.Set.empty, Typ.Var.Map.empty)
  | RequireVal(x, t) :: reqs ->
      let (env, dom_te, dom_ty, ex_vars) = wfreqs reqs in
      if Term.Var.Set.mem x.content dom_te
      then
        Error.raise_error Error.prog_wf x.startpos x.endpos
          "Duplicate term variable in a require statement."
      else begin
        match Wftype.check_wftype env t Kind.mkBase with
        | Answer.Yes ->
            (Env.Term.add_var x.content t env,
             Term.Var.Set.add x.content dom_te,
             dom_ty, ex_vars)
        | Answer.No reasons ->
            Error.raise_error Error.type_wf t.startpos t.endpos
              (error_msg reasons)
      end
  | RequireTyp(x, k) :: reqs ->
      let (env, dom_te, dom_ty, ex_vars) =  wfreqs reqs in
      if Typ.Var.Set.mem x.content dom_ty
      then
        Error.raise_error Error.prog_wf x.startpos x.endpos
          "Duplicate type variable in a require statement."
      else
        if Wftype.wfkind env k.content
        then
          (Env.Typ.add_var (locate_with Mode.U x) x.content k.content env,
           dom_te,
           Typ.Var.Set.add x.content dom_ty,
           ex_vars)
        else
          Error.raise_error Error.kind_wf k.startpos k.endpos
            "Ill-formed kind."
  | ExportTyp(x, k) :: reqs ->
      let (env, dom_te, dom_ty, ex_vars) =  wfreqs reqs in
      if Typ.Var.Set.mem x.content dom_ty
      then
        Error.raise_error Error.prog_wf x.startpos x.endpos
          "Duplicate type variable in an export statement."
      else
        if Wftype.wfkind env k.content
        then
          (Env.Typ.add_var (locate_with Mode.U x) x.content k.content env,
           dom_te,
           Typ.Var.Set.add x.content dom_ty,
           Typ.Var.Map.add x.content (locate_with Mode.E x) ex_vars)
        else
          Error.raise_error Error.kind_wf k.startpos k.endpos
            "Ill-formed kind."

let wfreqs r =
  let (env, _, _, s) = wfreqs r in (env, s)

let wfprog { reqs ; code } =
  let (env, ex_vars) = wfreqs reqs in
  let (env', t) = Wfterm.wfterm env code in
  let ex_vars' = Env.Typ.exist_vars env' in
    let unused_ex_vars = Ast.Typ.Var.Map.filter
        (fun x _ -> not (Ast.Typ.Var.Map.mem x ex_vars')) ex_vars in
      try
        let (_x, mode) = Ast.Typ.Var.Map.choose unused_ex_vars in
        Error.raise_error Error.prog_wf mode.startpos mode.endpos
          "This type variable is not exported by the program."
      with Not_found ->
        let unregistered_ex_vars = Ast.Typ.Var.Map.filter
            (fun x _ -> not (Ast.Typ.Var.Map.mem x ex_vars)) ex_vars' in
        try
          let (_x, mode) = Ast.Typ.Var.Map.choose unregistered_ex_vars in
          Error.raise_error Error.prog_wf mode.startpos mode.endpos
            "This type variable is exported by the program, but was not required to be exported."
        with Not_found ->
          t


