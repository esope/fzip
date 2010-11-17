(** Typeckecking of terms. *)
open Ast

val wfterm: Env.t -> Term.t -> Typ.t
val check_wfterm: Env.t -> Term.t -> Typ.t -> bool

