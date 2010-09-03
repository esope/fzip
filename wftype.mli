(** Checking types. *)
open Ast.Typ

type env = (typ, typ kind) Env.t

(** Decides subkinding. *)
val wfsubkind: env -> typ kind -> typ kind -> bool

(** Decides kind wellformedness. *)
val wfkind: env -> typ kind -> bool

(** Computes the minimal kind. *)
val wftype: env -> typ -> typ kind

(** Decides subtyping. *)
val wfsubtype: env -> typ -> typ -> bool
