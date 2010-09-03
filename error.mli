(* categories of errors *)
type t
val lexing: t
val parsing: t

val raise_error: t -> Lexing.position -> Lexing.position -> string -> 'a
