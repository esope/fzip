val string_of_token: Parser.token -> string

val get_current_start: unit -> Lexing.position
val get_current_end: unit -> Lexing.position
val get_current_token: unit -> Parser.token

val token: string -> Ulexing.lexbuf ->
  Parser.token * Lexing.position * Lexing.position
