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
    (FreeImpl: F_ATOM_IMPL) 
    (BoundImpl: B_ATOM_IMPL with type sort = FreeImpl.sort) :
    S with type sort = FreeImpl.sort =
  struct

    type sort = FreeImpl.sort
    type 'sort free = 'sort FreeImpl.t constraint 'sort = sort
    type 'sort bound = 'sort BoundImpl.t constraint 'sort = sort

    module Free = struct
      type sort = FreeImpl.sort
      type 'sort t = sort free constraint 'sort = sort
      let eq = FreeImpl.eq
      let fresh = FreeImpl.fresh
    end

    module Bound = struct
      type sort = BoundImpl.sort
      type 'sort t = sort bound constraint 'sort = sort
      let eq = BoundImpl.eq
    end

    module Abs = struct
      type ('sort, 'a) t = { var : sort bound ; body : 'a}
      constraint 'sort = sort

      let fmap f abs = { abs with body = f abs.body }
      let bmap f abs x u =
        if BoundImpl.eq abs.var x then abs else { abs with body = f abs.body x u }

      let hom f { var = y ; body = b } = f y b

      type 'a fsubst = 'a -> sort bound -> 'a -> 'a
      type 'a bsubst = 'a -> sort free -> 'a -> 'a

      let mk_instantiate
          (var_bsubst: 'term -> sort bound -> 'term -> 'term)
          (abs: (sort, 'term) t) (x: sort bound) (u: 'term) : 'term =
        var_bsubst abs.body abs.var u

      let list_max l = List.fold_left BoundImpl.max BoundImpl.zero l

(* height of Sato & Pollack *)
      let rec mk_h
          (hom: ((sort, 'term) t -> 'a) ->
            (sort free -> 'b) ->
              (sort bound -> 'b) ->
                ('b list -> 'b) -> 'term -> 'b)
          (x: sort free) : 'term -> sort bound =
            hom
              (fun abs ->
                let n = mk_h hom x abs.body in
                if BoundImpl.eq n BoundImpl.zero
                then BoundImpl.zero
                else BoundImpl.max n (BoundImpl.succ abs.var))
              (fun y ->
                if FreeImpl.eq x y then BoundImpl.succ BoundImpl.zero else BoundImpl.zero)
              (fun y -> BoundImpl.zero)
              list_max
              
      let mk_abs hom_tree subst bvar =
        let h = mk_h hom_tree in
        fun x t ->
          let n = h x t in
          { var = n ; body = subst t x (bvar n) }
    end
  end
