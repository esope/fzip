type t = int
let compare: int -> int -> int = compare
let equal: int -> int -> bool = ( = )
let hash: int -> int = Hashtbl.hash
