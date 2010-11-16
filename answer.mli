(** Handling of reasons of failures. *)

open Ast

type reason =
  | TYPES of Typ.t * Typ.t
        (** [TYPES(t1,t2)] means that [t1] is not a subtype of [t2]. *)

  | KINDS of Kind.t * Kind.t
        (** [KINDS(k1,k2)] means that [k1] is not a subkind of [k2]. *)

  | WF_TYPE of Typ.t * Kind.t
        (** [WF_TYPE(t,k)] means that [t] cannot be given the kind [k]. *)

  | E_TYP_VAR_PURE of Typ.Var.free Location.located
        (** [E_TYP_VAR_PURE a] means that [a] is an existential variable that is
            present in the current typing context. *)

  | TERM_VAR_DISAGREE of Term.Var.free Location.located
        (** [TERM_VAR_DISAGREE x] means that [x] is assigned two different types
            while zipping two contexts. *)

  | TYP_VAR_DISAGREE of Mode.mode Location.located * Typ.Var.free
        (** [TYP_VAR_DISAGREE (mode, a)] means that [a] is assigned two
            different kinds or modes while zipping two contexts. *)

type t = Yes | No of reason list

(** Chains two answers.
    If the left one is [No], then the second one is discarded. *)
val ( &*& ): t -> t -> t
val from_bool: bool -> t
val to_bool: t -> bool
val error_msg: reason list -> string

(** The same module, with a value in the positive case. *)
module WithValue : sig
  type 'a t = Yes of 'a | No of reason list

  val ( &*& ): 'a t -> 'a t -> 'a t
  val to_bool: 'a t -> bool
  val map: ('a -> 'b) -> 'a t -> 'b t
  val error_msg: reason list -> string
end
