open Ast

type reason =
  | TYPES of Typ.t * Typ.t
  | KINDS of Kind.t * Kind.t
  | WF_TYPE of Typ.t * Kind.t
type t = Yes | No of reason list

val ( &*& ): t -> t -> t
val from_bool: bool -> t
val to_bool: t -> bool
val error_msg: reason list -> string

module WithValue : sig
  type 'a t = Yes of 'a | No of reason list

  val ( &*& ): 'a t -> 'a t -> 'a t
  val to_bool: 'a t -> bool
  val map: ('a -> 'b) -> 'a t -> 'b t
  val error_msg: reason list -> string
end
