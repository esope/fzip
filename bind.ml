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

module type PRE_ATOM = sig
  type sort
  type 'sort t constraint 'sort = sort
  val eq: sort t -> sort t -> bool
end

module type B_ATOM = PRE_ATOM
module type F_ATOM = sig
  include PRE_ATOM
  val fresh: unit -> sort t
end

module type S = sig
  type sort
  type 'sort free constraint 'sort = sort
  type 'sort bound constraint 'sort = sort
  module F : F_ATOM with type sort = sort with type 'a t = 'a free
  module B : B_ATOM with type sort = sort with type 'a t = 'a bound
  module Abs : sig
    type ('sort, 'a) t constraint 'sort = sort
    val map: ('a -> 'b) -> (sort, 'a) t -> (sort, 'b) t
    val hom: (sort bound -> 'a -> 'b) -> (sort, 'a) t -> 'b
    val mk_bsubst: ('a -> sort bound -> 'a -> 'a) ->
           (sort, 'a) t -> sort bound -> 'a -> (sort, 'a) t
    val mk_h: ((sort free -> sort bound -> sort bound) ->
            (sort bound -> sort bound -> sort bound) ->
            (sort bound list -> sort bound) ->
            (sort bound -> sort bound) -> 'a -> sort bound -> sort bound) ->
           sort bound -> (sort, 'a) t -> sort bound
  end
end

module Make
    (Free: F_ATOM_IMPL) 
    (Bound: B_ATOM_IMPL with type sort = Free.sort) :
    S with type sort = Free.sort = struct

      type sort = Free.sort
      type 'sort free = 'sort Free.t constraint 'sort = sort
      type 'sort bound = 'sort Bound.t constraint 'sort = sort

      module F = struct
        type sort = Free.sort
        type 'sort t = sort free constraint 'sort = sort
        let eq = Free.eq
        let fresh = Free.fresh
      end

      module B = struct
        type sort = Bound.sort
        type 'sort t = sort bound constraint 'sort = sort
        let eq = Bound.eq
      end

      module Abs = struct
        type ('sort, 'a) t = { var : sort bound ; body : 'a}
        constraint 'sort = sort

        let map f { var = x ; body = b } = { var = x ; body = f b }

        let hom f { var = y ; body = b } = f y b

        let list_max l = List.fold_left Bound.max Bound.zero l

        let mk_bsubst (f: 'a -> sort bound -> 'a -> 'a)
            (abs : (sort, 'a) t) (x: sort bound) (t: 'a) =
          if Bound.eq abs.var x
          then abs
          else { abs with body = f abs.body x t }

        let h_abs (f: sort bound -> 'a -> sort bound) (x: sort bound)
            (abs : (sort, 'a) t) : sort bound =
          let n = f x abs.body in
          if Bound.eq n Bound.zero
          then Bound.zero
          else Bound.max n (Bound.succ abs.var)

        let h_free (x: sort bound) (_: sort free) = Bound.zero
        let h_bound (x: sort bound) (y: sort bound) =
          if Bound.eq x y
          then Bound.succ Bound.zero
          else Bound.zero

(* height of Sato & Pollack *)
        let rec mk_h (hom: (sort free -> 'a -> 'b) ->
          (sort bound -> 'a -> 'b) ->
            ('b list -> 'b) -> ('b -> 'b) -> 'term -> 'a -> 'b)
            (x: sort bound) (abs: (sort, 'term) t) : sort bound =
          h_abs
            (fun x t ->
              hom
                (fun x y -> h_free y x)
                h_bound
                list_max
                (fun y -> mk_h hom y abs)
                t x)
            x abs


      end

    end
