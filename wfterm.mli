(** Typeckecking of terms. *)
open Ast

type env = (Typ.t, Kind.t) Env.t

val wfterm: env -> Term.t -> Typ.t
val check_wfterm: env -> Term.t -> Typ.t -> bool

