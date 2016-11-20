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

  (** comparison *)
  val compare: free -> free -> int

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

  (** comparison *)
  val bcompare: bound -> bound -> int

  (** [bmax] computes the maximem of two bound variables.
      The string representation of the result is the one of
      the first argument. *)
  val bmax: bound -> bound -> bound
  val bto_string: bound -> string

  module BSet: Set.S with type elt = bound
  module BMap: Map.S with type key = bound
  module Set : Set.S with type elt = free
  module Map : Map.S with type key = free

  (** Helper module that helps finding the "best" free name for a
      given bound name. This is useful for pretty printing. *)
  module Best : sig
    (** The type of datastructure that remember the best names. *)
    type t

    (** The structure in which nothing is recorded. *)
    val empty: t

    (** Get the best name. *)
    val get: t -> bound -> free

    (** Get the best name and registers it. Typically, you should call
        that function when traversing a binder. *)
    val remember_get: t -> bound -> t * free
  end

end

module Make (Default: CONFIG) : S
