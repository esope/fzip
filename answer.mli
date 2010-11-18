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

  | TERM_VAR_DISAGREE_TYP of
      Typ.t * Typ.t * Term.Var.free
        (** [TERM_VAR_DISAGREE_TYP (t1, t2, x)] means that [x] is assigned
            two different types [t1] and [t2] while zipping two
            contexts. *)

  | TYP_VAR_DISAGREE_KIND of
      Kind.t Location.located * Kind.t Location.located * Typ.Var.free
        (** [TYP_VAR_DISAGREE_KIND (k1, k2, x)] means that [x] is assigned
            two different kinds [k1] and [k2] while zipping two
            contexts. *)

  | TYP_VAR_DISAGREE_EE of
      Mode.mode Location.located * Mode.mode Location.located * Typ.Var.free
        (** [TYP_VAR_DISAGREE_EE (mode1, mode2, x)] means that [x] is assigned
            the modes [mode1 = E] and [mode2 = E] while zipping two
            contexts. *)

  | TYP_VAR_DISAGREE_UE of
      Mode.mode Location.located * Mode.mode Location.located * Typ.Var.free
        (** [TYP_VAR_DISAGREE_UE (mode1, mode2, x)] means that [x] is assigned
            the modes [mode1 = U] and [mode2 = E] while zipping two
            contexts. *)

  | TYP_VAR_DISAGREE_EEQ of
      Mode.mode Location.located * Mode.mode Location.located * Typ.Var.free
        (** [TYP_VAR_DISAGREE_EEQ (mode1, mode2, x)] means that [x] is assigned
            the modes [mode1 = E] and [mode2 = EQ t] while zipping two
            contexts. *)

  | TYP_VAR_DISAGREE_EQE of
      Mode.mode Location.located * Mode.mode Location.located * Typ.Var.free
        (** [TYP_VAR_DISAGREE_EQE (mode1, mode2, x)] means that [x] is assigned
            the modes [mode1 = EQ t] and [mode2 = E] while zipping two
            contexts. *)

  | TYP_VAR_DISAGREE_UEQ of
      Mode.mode Location.located * Mode.mode Location.located * Typ.Var.free
        (** [TYP_VAR_DISAGREE_UEQ (mode1, mode2, x)] means that [x] is assigned
            the modes [mode1 = U] and [mode2 = EQ t] while zipping two
            contexts. *)

  | TYP_VAR_DISAGREE_EQU of
      Mode.mode Location.located * Mode.mode Location.located * Typ.Var.free
        (** [TYP_VAR_DISAGREE_EQU (mode1, mode2, x)] means that [x] is assigned
            the modes [mode1 = EQ] and [mode2 = U] while zipping two
            contexts. *)

  | TYP_VAR_DISAGREE_EQEQ of
      Mode.mode Location.located * Mode.mode Location.located * Typ.Var.free
        (** [TYP_VAR_DISAGREE_EQEQ (mode1, mode2, x)] means that [x]
            is assigned the modes [mode1 = EQ t1] and [mode2 = EQ t2]
            where [t1] and [t2] are two different types while zipping
            two contexts. *)

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
