(** Typeckecking of terms. *)
open Ast

(** [wfterm G e] returns [(G', t)] where t is the minimal type of [t]
    and [G'] is the minimal environment in which [e] is welltyped. It
    can contain bindings that are marked as existential. It requires
    that [G] is a pure, wellformed environment. Invariant: if [G ok]
    and [wfterm G e = (G', t)], then [G' |- e : t] holds. *)
val wfterm: Env.t -> Term.t -> Env.t * Typ.t

val check_wfterm: Env.t -> Term.t -> Typ.t -> bool
