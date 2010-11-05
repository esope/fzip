module type CONFIG = sig
  val fbase: string
  val bbase: string
end

module type S = sig
  (** free variables *)
  type free
        (** bound variables *)
  type bound
        (** equality test *)
  val eq: free -> free -> bool 
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
  val bzero: bound
  val bone: bound
  val bsucc: bound -> bound
  val beq: bound -> bound -> bool
  val bmax: bound -> bound -> bound
  val bto_string: bound -> string
end

module Make (Default: CONFIG) : S
