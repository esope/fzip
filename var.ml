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

module Make (Default: sig val fbase: string val bbase: string end) : S = struct
  type free = string * int
  type bound = int
  let eq (x,n) (y,m) = MyString.equal x y && MyInt.equal n m
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
  let bfresh _bvar = fresh ()
  let bzero = 0
  let bone = 1
  let bsucc = (+) 1
  let beq: int -> int -> bool = (=)
  let bmax: int -> int -> int = max
  let bto_string n = Default.bbase ^ (string_of_int n)
end