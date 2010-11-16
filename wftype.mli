(** Checking types. *)
open Ast

type env = (Typ.t, Kind.t) Env.t

(** Decides kind wellformedness. *)
val wfkind: env -> Kind.t -> bool

(** Decides subkinding. *)
val sub_kind: unfold_eq:bool -> env -> Kind.t -> Kind.t -> Answer.t
val sub_kind_b: unfold_eq:bool -> env -> Kind.t -> Kind.t -> bool

(** Computes the minimal kind. *)
val wftype: env -> Typ.t -> Kind.t
val check_wftype: env -> Typ.t -> Kind.t -> bool

(** Decides subtyping. *)
val sub_type: unfold_eq:bool -> env -> Typ.t -> Typ.t -> Answer.t
val sub_type_b: unfold_eq:bool -> env -> Typ.t -> Typ.t -> bool
