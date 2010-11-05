(** Checking types. *)
open Ast.Typ

type env = (typ, typ kind) Env.t

(** Decides subkinding. *)
val wfsubkind: env -> typ kind -> typ kind -> Answer.t
val wfsubkind_b: env -> typ kind -> typ kind -> bool

(** Decides kind wellformedness. *)
val wfkind: env -> typ kind -> bool

(** Computes the minimal kind. *)
val wftype: env -> typ -> typ kind

(** Decides subtyping. *)
val wfsubtype: env -> typ -> typ -> Answer.t
val wfsubtype_b: env -> typ -> typ -> bool
