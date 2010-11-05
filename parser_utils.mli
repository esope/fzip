(** Useful functions related to parsing. *)

open Ast

module String : sig
  module Raw : sig
    open Raw
    val parse_typ: string -> typ
    val parse_kind: string -> typ kind
    val parse_term: string -> (typ kind, typ) term
  end

  val parse_typ: string -> Typ.typ
  val parse_kind: string -> Typ.typ Typ.kind
  val parse_term: string -> Term.term

end

module Channel : sig
  module Raw : sig
    open Raw
    val parse_typ: in_channel -> string -> typ
    val parse_kind: in_channel -> string -> typ kind
    val parse_term: in_channel -> string -> (typ kind, typ) term
  end

  val parse_typ: in_channel -> string -> Typ.typ
  val parse_kind: in_channel -> string -> Typ.typ Typ.kind
  val parse_term: in_channel -> string -> Term.term

end
