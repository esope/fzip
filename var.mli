(** Abstract variables, free and bound. *)

module type CONFIG = sig
  val fbase: string
  val bbase: string
end

module type S = sig

  (** type of free variables *)
  type free

  (** type of bound variables *)
  type bound

  (** equality test *)
  val equal: free -> free -> bool 

  (** creation of a free variable from a base name *)
  val make: string -> free

  (** for pretty printing purposes only, gets the base name *)
  val to_string: free -> string

  (** creation of free variables from a base name, from a free variable,
      or from nothing *)

  val sfresh: string -> free
  val ffresh: free -> free
  val bfresh: bound -> free
  val fresh: unit -> free

  (** unsafe functions *)

  val bzero: free -> bound
  val bone: free -> bound
  val bzerob: bound -> bound
  val boneb: bound -> bound
  val bzero_default: bound
  val bone_default: bound
  val bsucc: bound -> bound
  val bequal: bound -> bound -> bool
  val bequal_bzero: bound -> bool
  val bmax: bound -> bound -> bound
  val bto_string: bound -> string

  module Set : Set.S with type elt = free
  module Map: Map.S with type key = free
end

module Make (Default: CONFIG) : S
