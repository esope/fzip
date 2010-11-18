(** Checking types. *)
open Ast

(** Decides kind wellformedness. *)
val wfkind: Env.t -> Kind.t -> bool

(** Decides subkinding. *)
val sub_kind: unfold_eq:bool -> Env.t -> Kind.t -> Kind.t -> Answer.t
val sub_kind_b: unfold_eq:bool -> Env.t -> Kind.t -> Kind.t -> bool

(** Computes the minimal kind. *)
val wftype: Env.t -> Typ.t -> Kind.t
val check_wftype: Env.t -> Typ.t -> Kind.t -> Answer.t
val check_wftype_b: Env.t -> Typ.t -> Kind.t -> bool

(** Decides subtyping. *)
val sub_type: unfold_eq:bool -> Env.t -> Typ.t -> Typ.t -> Answer.t
val sub_type_b: unfold_eq:bool -> Env.t -> Typ.t -> Typ.t -> bool

