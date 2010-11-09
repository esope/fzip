include module type of MyString

module Set : Set.S with type elt = t
module Map : Map.S with type key = t
module AList : sig
  type key = t
  type 'a t = (key * 'a) list
  val empty: 'a t
  val singleton: key -> 'a -> 'a t
  val add: key -> 'a -> 'a t -> 'a t
  val find: key -> 'a t -> 'a
  val mem: key -> 'a t -> bool
  val map: ('a -> 'b) -> 'a t -> 'b t
  val mapi: (key -> 'a -> key * 'b) -> 'a t -> 'b t
  val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val equal: ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
end
