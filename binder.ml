module type B_ATOM_IMPL = sig
  type t
  val zero: t
  val succ: t -> t
  val eq: t -> t -> bool
  val max: t -> t -> t
  val to_string: t -> string
end

module type F_ATOM_IMPL = sig
  type t
  val eq: t -> t -> bool
  val fresh: unit -> t
  val to_string: t -> string
end

module type ATOM = sig
  type bvar
  type atom
  type 'a abs
  val eq: atom -> atom -> bool
  val beq: bvar -> atom -> bool
  val is_free: atom -> bool
  val fresh: unit -> atom
  val to_string: atom -> string

  (* These two functions are needed to compute canonical representations. *)

  (* The Sato-Pollack height function *)
  val h: atom -> atom -> bvar

  (* This function is needed to compute the h function on datatypes *)
  val max: bvar -> bvar -> bvar

  module Abs: sig
    type ('a, 'b, 'c) op = 'a -> 'b -> 'c -> 'a
    type ('a, 'b) subst = ('a, atom, 'b) op
    type 'a rename = ('a, atom) subst
    type ('a, 'b) bsubst = ('a, bvar, 'b) op
    type 'a brename = ('a, atom) bsubst

    val subst: ('a, 'b) subst -> ('a abs, 'b) subst
    val rename: 'a rename -> ('a abs) rename
    val bsubst: ('a, 'b) bsubst -> ('a abs, 'b) bsubst
    val brename: 'a brename -> ('a abs) brename

    val var_map: ((atom -> 'a) -> 'a -> 'a) -> (atom -> 'a) -> 'a abs -> 'a abs

(* this function is unsafe, but is provided for efficiency reasons *)
    val hom: ('a -> 'b) -> 'a abs -> 'b

    val inst: ('a, 'a) bsubst -> 'a abs -> 'a -> 'a

    type 'a h = atom -> 'a -> bvar
    val h: 'a h -> ('a abs) h

    val make: 'a h -> 'a rename -> atom -> 'a -> 'a abs
    val destruct: 'a brename -> 'a abs -> (atom * 'a)

    type 'a eq = 'a -> 'a -> bool
    val eq: 'a eq -> ('a abs) eq
  end

end

module MakeGen(Bound: B_ATOM_IMPL)(Free: F_ATOM_IMPL) : ATOM =
  struct

    type fvar = Free.t
    type bvar = Bound.t
    type atom = Free of fvar | Bound of bvar
    type 'a abs = Abs of Bound.t * 'a

    let max = Bound.max
    let fresh () = Free (Free.fresh ())

    let to_string = function
      | Free x -> Free.to_string x
      | Bound x -> Bound.to_string x

    let eq a b = match (a, b) with
    | (Free a, Free b) -> Free.eq a b
    | (Bound a, Bound b) -> Bound.eq a b
    | _ -> false

    let beq x = function
      | Bound y -> Bound.eq x y
      | _ -> false

    let is_free = function
      | Free _ -> true
      | Bound _ -> false

    let zero = Bound.zero
    let one = Bound.succ Bound.zero
    let h a b = match (a, b) with
    | (Free a, Free b)  -> if Free.eq a b then one else zero
    | (Free a, Bound b) -> zero
    | _ -> assert false

    module Abs = struct
      type ('a, 'b, 'c) op = 'a -> 'b -> 'c -> 'a
      type ('a, 'b) subst = ('a, atom, 'b) op
      type 'a rename = ('a, atom) subst
      type ('a, 'b) bsubst = ('a, bvar, 'b) op
      type 'a brename = ('a, atom) bsubst

      let subst body_subst (Abs (y, body)) (x: atom) u =
        Abs (y, body_subst body x u)

      let bsubst body_bsubst (Abs (y, body) as abs) x u =
        if Bound.eq x y
        then abs
        else Abs (y, body_bsubst body x u)

      let rename body_rename (Abs (z, body) as abs) x y =
        match x with
        | Free _ -> Abs(z, body_rename body x y)
        | Bound x when Bound.eq x z -> abs
        | Bound _ -> Abs (z, body_rename body x y)

      let brename body_brename (Abs (z, body) as abs) x y =
        if Bound.eq x z then abs
        else Abs (z, body_brename body x y)

      let var_map body_map f (Abs (z, body)) =
        Abs(z, body_map f body)

      let hom body_hom (Abs (_, body)) =
        body_hom body

      type 'a inst = 'a abs -> 'a -> 'a
      let inst body_bsubst (Abs (y, body)) u =
        body_bsubst body y u

      type 'a h = atom -> 'a -> bvar
      let h body_h x (Abs (y, body)) =
        let n = body_h x body in
        if Bound.eq zero n
        then zero
        else Bound.max n (Bound.succ y)

      let make body_h body_rename x t =
        let y = body_h x t in Abs (y, body_rename t x (Bound y))
          
      let destruct body_brename (Abs (x, t)) =
        let y = fresh () in
        (* using the "zero" property of h *)
        if Bound.eq x Bound.zero
        then (y, t)
        else (y, body_brename t x y)

      type 'a eq = 'a -> 'a -> bool
      let eq body_eq (Abs (x, t)) (Abs (x', t')) =
        Bound.eq x x' && body_eq t t'
    end

  end

module IntAtom : B_ATOM_IMPL =
struct
  type t = int
  let zero = 0
  let succ x = x + 1
  let max (x: int) (y: int) = max x y
  let eq (x: int) (y: int) = x = y
  let to_string x = "__x" ^ (string_of_int x)
end

module Make(X: F_ATOM_IMPL): ATOM = MakeGen(IntAtom)(X)
