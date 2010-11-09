(** Checking types. *)
open Ast.Typ

type env = (typ, typ kind) Env.t

(** Decides kind wellformedness. *)
val wfkind: env -> typ kind -> bool

(** Decides subkinding. *)
val sub_kind: env -> typ kind -> typ kind -> Answer.t
val sub_kind_b: env -> typ kind -> typ kind -> bool

(** Computes the minimal kind. *)
val wftype: env -> typ -> typ kind
val check_wftype: env -> typ -> typ kind -> bool

(** Decides subtyping. *)
val sub_type: env -> typ -> typ -> Answer.t
val sub_type_b: env -> typ -> typ -> bool
