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
end

module Decode : sig
  open Ast

  module Typ : sig
    open Raw
    val typ: Typ.typ -> typ
    val kind: Typ.typ Typ.kind -> typ kind
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

    open Ast.Typ
    val channel: Pprint.Channel.channel -> typ -> unit
    val buffer: Pprint.Buffer.channel -> typ -> unit
    val string: typ -> string
  end

  module Kind : sig
    module Raw : sig
      val channel: Pprint.Channel.channel -> typ kind -> unit
      val buffer: Pprint.Buffer.channel -> typ kind -> unit
      val string: typ kind -> string
    end

    open Ast.Typ
    val channel: Pprint.Channel.channel -> typ kind -> unit
    val buffer: Pprint.Buffer.channel -> typ kind -> unit
    val string: typ kind -> string
  end

end
