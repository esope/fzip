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
  val bmax: bound -> bound -> bound
  val bto_string: bound -> string

  module BSet: Set.S with type elt = bound
  module BMap: Map.S with type key = bound
  module Set : Set.S with type elt = free
  module Map : Map.S with type key = free
end

module Make (Default: sig val fbase: string val bbase: string end) : S = struct

  type free = string * int

  type bound = int * free
        (* We record the representation of the free var for pretty
           printing purpose. The comparisions will be all made against
           the first component only. *)

  let equal (x,n) (y,m) = MyString.equal x y && MyInt.equal n m
  let compare (s1, i1) (s2, i2) =
    let n_s = String.compare s1 s2 in
    if n_s = 0 then compare i1 i2 else n_s
  let make s = (s,0)
  let to_string (s,n) = if n = 0 then s else (s ^ (string_of_int n))
  module H = Hashtbl.Make(MyString)
  let h = H.create 256
  let sfresh s =
    let n = try H.find h s with Not_found -> 0 in
    H.replace h s (n+1) ;
    (s, n+1)
  let ffresh (s,_) = sfresh s
  let fresh () = sfresh Default.fbase
  let bfresh (_, free) = ffresh free
  let bzero free = (0, free)
  let bone free = (1, free)
  let bzerob (_, free) = (0, free)
  let boneb (_, free) = (1, free)
  let bzero_default = (0, (Default.bbase, 0))
  let bone_default = (1, (Default.bbase, 0))
  let bsucc (i, f) = (i + 1, f)
  let bequal: bound -> bound -> bool = fun x y -> (fst x) = (fst y)
  let bequal_bzero (i, _) = i = 0
  let bcompare : bound -> bound -> int = fun b1 b2 ->
    MyInt.compare (fst b1) (fst b2)
  let bmax: bound -> bound -> bound = fun x y ->
    if (fst x) <= (fst y) (* we keep the name of the first argument *)
    then (fst y, snd x)
    else (fst x, snd x)

  let bto_string (n, f) = to_string (fst f, if n = 0 then 0 else n-1)

  module Bound = struct
    type t = bound
    let compare = bcompare
  end
  module BSet = Set.Make(Bound)
  module BMap = Map.Make(Bound)

  module Free = struct
    type t = free
    let compare = compare
  end
  module Set = Set.Make(Free)
  module Map = Map.Make(Free)

end
