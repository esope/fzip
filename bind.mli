module type B_ATOM_IMPL = sig
  type sort
  type 'sort t constraint 'sort = sort
  val zero: sort t
  val succ: sort t -> sort t
  val eq: sort t -> sort t -> bool
  val max: sort t -> sort t -> sort t
end

module type F_ATOM_IMPL = sig
  type sort
  type 'sort t constraint 'sort = sort
  val eq: sort t -> sort t -> bool
  val fresh: unit -> sort t
end

module type B_ATOM = sig
  type sort
  type 'sort t constraint 'sort = sort
  val eq: sort t -> sort t -> bool
end

module type F_ATOM = sig
  include B_ATOM
  val fresh: unit -> sort t
end

module type S = sig
  type sort
  type 'sort free constraint 'sort = sort
  type 'sort bound constraint 'sort = sort
  module Free : F_ATOM with type sort = sort with type 'a t = 'a free
  module Bound : B_ATOM with type sort = sort with type 'a t = 'a bound
  module Abs : sig
    type ('sort, 'a) t constraint 'sort = sort
    val fmap: ('a -> 'b) -> (sort, 'a) t -> (sort, 'b) t
    val bmap: ('a -> sort bound -> 'b -> 'a) ->
      (sort, 'a) t -> sort bound -> 'b -> (sort, 'a) t
    val hom: (sort bound -> 'a -> 'b) -> (sort, 'a) t -> 'b

    type 'a fsubst = 'a -> sort bound -> 'a -> 'a
    type 'a bsubst = 'a -> sort free -> 'a -> 'a

    val mk_instantiate: 'a fsubst -> (sort, 'a) t -> sort bound -> 'a -> 'a
    val mk_abs: (((sort, 'a) t -> sort bound) ->
      (sort free -> sort bound) ->
        (sort bound -> sort bound) ->
          (sort bound list -> sort bound) -> 'a -> sort bound) ->
            'a bsubst ->
              (sort bound -> 'a) -> sort free -> 'a -> (sort, 'a) t
  end
end

module Make
    (Free: F_ATOM_IMPL) 
    (Bound: B_ATOM_IMPL with type sort = Free.sort) :
    S with type sort = Free.sort
