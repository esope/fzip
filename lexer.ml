open Parser
open Ulexing

let current_bol = ref 0 (* global position *)
let current_lnum = ref 1
let current_file = ref "<dummy>"
let current_start = ref Lexing.dummy_pos
let current_end = ref Lexing.dummy_pos
let current_token = ref (ID "dummy")

(* accessors *)
let get_current_start () = !current_start
let get_current_end () = !current_end
let get_current_token () = !current_token

let break_line lexbuf =
  incr current_lnum ; current_bol := lexeme_start lexbuf
let startpos lexbuf =
  { Lexing.pos_fname = !current_file ;
    Lexing.pos_lnum = !current_lnum ;
    Lexing.pos_bol = !current_bol ;
    Lexing.pos_cnum = lexeme_start lexbuf }
let endpos lexbuf =
  { Lexing.pos_fname = !current_file ;
    Lexing.pos_lnum = !current_lnum ;
    Lexing.pos_bol = !current_bol ;
    Lexing.pos_cnum = lexeme_end lexbuf }
let locate lexbuf token =
  let startpos = startpos lexbuf
  and endpos = endpos lexbuf in
  current_start := startpos ;
  current_end := endpos ;
  current_token := token ;
  (token, startpos, endpos)

exception Lexing_error of Lexing.position * Lexing.position * string

let lexing_error_handler f file lexbuf =
  current_lnum := 1 ; current_bol := 0 ; current_file := file ;
  try f lexbuf
  with Lexing_error(startpos, endpos, s) ->
    Error.raise_error Error.lexing startpos endpos
      (Printf.sprintf "Unknown token: %s." s)

let regexp whitespace = ['\t' ' ']+
let regexp linebreak = ['\n']
let regexp low_greek = [945-969]
let regexp up_greek = [913-937]
let regexp greek = low_greek | up_greek
let regexp low_alpha = ['a'-'z']
let regexp up_alpha =  ['A'-'Z']
let regexp alpha = low_alpha | up_alpha
let regexp alpha_greek = alpha | greek
let regexp digit = ['0'-'9']
let regexp id = alpha_greek+ (alpha_greek | digit)*

let rec token = lexer
| whitespace -> token lexbuf
| linebreak -> break_line lexbuf ; token lexbuf
| "=>" | 8658 (* ⇒ *) -> locate lexbuf DBLARROW
| "->" | 8594 (* → *) -> locate lexbuf ARROW
| "*" | 8902 (* ⋆ *) -> locate lexbuf STAR
| "fun" | 955 (* λ *) -> locate lexbuf LAMBDA
| "Fun" | 923 (* Λ *) -> locate lexbuf UPLAMBDA
| "forall" | 8704 (* ∀ *) -> locate lexbuf FORALL
| "::" -> locate lexbuf DBLCOLON
| ":" -> locate lexbuf COLON
| ";" -> locate lexbuf SEMICOLON
| "(" -> locate lexbuf LPAR
| ")" -> locate lexbuf RPAR
| "." -> locate lexbuf DOT
| "," -> locate lexbuf COMMA
| "<" -> locate lexbuf LANGLE
| ">" -> locate lexbuf RANGLE
| "{" -> locate lexbuf LBRACE
| "}" -> locate lexbuf RBRACE
| "[" -> locate lexbuf LBRACKET
| "]" -> locate lexbuf RBRACKET
| "=" -> locate lexbuf EQ
| 215 (* × *) -> locate lexbuf TIMES
| "Pi" | 928 (* Π *) -> locate lexbuf PI
| "Sigma" |  931 (* Σ *) -> locate lexbuf SIGMA
| "S" -> locate lexbuf SINGLE
| eof -> locate lexbuf EOF
| id -> locate lexbuf (ID (utf8_lexeme lexbuf))
| _ ->
    raise (Lexing_error (startpos lexbuf,
                         endpos lexbuf,
                         utf8_lexeme lexbuf))

let token = lexing_error_handler token

let string_of_token = function
  | ID x -> x
  | LAMBDA -> "λ"
  | UPLAMBDA -> "Λ"
  | LPAR -> "("
  | RPAR -> ")"
  | DBLCOLON -> "::"
  | APP -> ""
  | STAR -> "⋆"
  | DBLARROW -> "⇒"
  | COMMA -> ","
  | DOT -> "."
  | LANGLE -> "<"
  | RANGLE -> ">"
  | TIMES -> "×"
  | SINGLE -> "S"
  | PI -> "Π"
  | SIGMA -> "Σ"
  | COLON -> ":"
  | SEMICOLON -> ";"
  | LBRACE -> "{"
  | RBRACE -> "}"
  | LBRACKET -> "["
  | RBRACKET -> "]"
  | EQ -> "="
  | FORALL -> "∀"
  | ARROW -> "→"
  | EOF -> "\n"
