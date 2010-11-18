(** Useful functions on ASTs. *)

open Ast
open Location

module Encode : sig
  open Ast

  module Typ : sig
    open Typ
    val typ: Raw.typ -> typ
    val kind: Raw.typ Raw.kind -> typ kind
  end

  module Term : sig
    open Ast.Term
    val term: (Raw.typ Raw.kind, Raw.typ) Raw.term -> term
  end

  module Prog : sig
    open Ast.Prog
    val prog: Raw.prog -> t
  end
end

module Decode : sig
  open Ast

  module Typ : sig
    open Raw
    val typ: Typ.t -> typ
    val kind: Kind.t -> typ kind
  end
end

module PPrint : sig
  open Ast.Raw
  type doc = Pprint.document

  val typ: typ -> doc
  val kind: typ kind -> doc

  module Typ : sig
    module Raw : sig
      val channel: Pprint.Channel.channel -> typ -> unit
      val buffer: Pprint.Buffer.channel -> typ -> unit
      val string: typ -> string
    end

    open Ast
    val channel: Pprint.Channel.channel -> Typ.t -> unit
    val buffer: Pprint.Buffer.channel -> Typ.t -> unit
    val string: Typ.t -> string
  end

  module Kind : sig
    module Raw : sig
      val channel: Pprint.Channel.channel -> typ kind -> unit
      val buffer: Pprint.Buffer.channel -> typ kind -> unit
      val string: typ kind -> string
    end

    open Ast
    val channel: Pprint.Channel.channel -> Kind.t -> unit
    val buffer: Pprint.Buffer.channel -> Kind.t -> unit
    val string: Kind.t -> string
  end

end
