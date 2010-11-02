open Ast.Typ

type reason = TYPES of typ * typ | KINDS of typ kind * typ kind
type t = Yes | No of reason list

val ( &*& ): t -> t -> t
val from_bool: bool -> t
val to_bool: t -> bool
val error_msg: reason list -> string

module WithValue : sig
  type 'a t = Yes of 'a | No of reason list

  val ( &*& ): 'a t -> 'a t -> 'a t
  val to_bool: 'a t -> bool
  val error_msg: reason list -> string
end
