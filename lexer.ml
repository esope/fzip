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
  incr current_lnum ; current_bol := lexeme_end lexbuf
let startpos lexbuf =
  { Lexing.pos_fname = !current_file ;
    Lexing.pos_lnum = !current_lnum ;
    Lexing.pos_bol = !current_bol ;
    Lexing.pos_cnum = lexeme_start lexbuf - !current_bol }
let endpos lexbuf =
  { Lexing.pos_fname = !current_file ;
    Lexing.pos_lnum = !current_lnum ;
    Lexing.pos_bol = !current_bol ;
    Lexing.pos_cnum = lexeme_end lexbuf - !current_bol }
let locate lexbuf token =
  let startpos = startpos lexbuf
  and endpos = endpos lexbuf in
  current_start := startpos ;
  current_end := endpos ;
  current_token := token ;
  (token, startpos, endpos)

exception Lexing_error of Lexing.position * Lexing.position * string
exception Unterminated_comment of Lexing.position * Lexing.position
exception Unexpected_end_of_comment of Lexing.position * Lexing.position


let lexing_error_handler f file lexbuf =
  current_file := file ;
  try f lexbuf
  with Lexing_error(startpos, endpos, s) ->
    Error.raise_error Error.lexing startpos endpos
      (Printf.sprintf "Unknown token: %s." s)
  | Unterminated_comment(startpos, endpos) ->
    Error.raise_error Error.lexing startpos endpos
      "Unterminated comment."
  | Unexpected_end_of_comment(startpos, endpos) ->
    Error.raise_error Error.lexing startpos endpos
      "Unexpected end of comment."


let regexp whitespace = ['\t' ' ']+
let regexp linebreak = ['\n' '\r' "\r\n"]
let regexp low_greek = [945-969]
let regexp up_greek = [913-937]
let regexp greek = low_greek | up_greek
let regexp low_alpha = ['a'-'z']
let regexp up_alpha =  ['A'-'Z']
let regexp alpha = low_alpha | up_alpha
let regexp alpha_greek = alpha | greek
let regexp digit = ['0'-'9']
let regexp id =
  alpha_greek+ ((alpha_greek | digit)* | (['_']+ (alpha_greek | digit)+))

let rec token = lexer
| whitespace -> token lexbuf
| linebreak -> break_line lexbuf ; token lexbuf
| "(*" -> comment 0 lexbuf
| "*)" -> raise (Unexpected_end_of_comment (startpos lexbuf, endpos lexbuf))
| "=>" | 8658 (* ⇒ *) -> locate lexbuf DBLARROW
| "->" | 8594 (* → *) -> locate lexbuf ARROW
| "*" | 8902 (* ⋆ *) | 9733 (* ★ *) -> locate lexbuf STAR
| "val" -> locate lexbuf VAL
| "type" -> locate lexbuf TYPE
| "as" -> locate lexbuf AS
| "fun" | 955 (* λ *) -> locate lexbuf LAMBDA
| "Fun" | 923 (* Λ *) -> locate lexbuf UPLAMBDA
| "let" -> locate lexbuf LET
| "in" -> locate lexbuf IN
| "rec" -> locate lexbuf REC
| "forall" | 8704 (* ∀ *) -> locate lexbuf FORALL
| "exists" | 8707 (* ∃ *) -> locate lexbuf EXISTS
| "::" -> locate lexbuf DBLCOLON
| ":" -> locate lexbuf COLON
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
| "Pi" | 928 (* Π *) -> locate lexbuf PI
| "sigma" |  931 (* Σ *) -> locate lexbuf SIGMA
| "nu" |  957 (* ν *) -> locate lexbuf NU
| "open" -> locate lexbuf OPEN
| "S" -> locate lexbuf SINGLE
| "import" -> locate lexbuf IMPORT
| "export" -> locate lexbuf EXPORT
| eof -> locate lexbuf EOF
| id -> locate lexbuf (ID (utf8_lexeme lexbuf))
| _ ->
    raise (Lexing_error (startpos lexbuf,
                         endpos lexbuf,
                         utf8_lexeme lexbuf))

and comment level = lexer
| "(*" -> comment (level+1) lexbuf
| "*)" ->
    assert (level >= 0) ;
    if level >=1
    then comment (level-1) lexbuf
    else token lexbuf
| linebreak -> break_line lexbuf ; comment level lexbuf
| eof ->
    raise (Unterminated_comment (startpos lexbuf, endpos lexbuf))
| _ -> comment level lexbuf


let token = lexing_error_handler token

let string_of_token = function
  | ID x -> x
  | VAL -> "val"
  | TYPE -> "type"
  | AS -> "as"
  | LAMBDA -> "λ"
  | UPLAMBDA -> "Λ"
  | LET -> "let"
  | REC -> "rec"
  | IN -> "in"
  | LPAR -> "("
  | RPAR -> ")"
  | DBLCOLON -> "::"
  | STAR -> "⋆"
  | DBLARROW -> "⇒"
  | DOT -> "."
  | COMMA -> ","
  | LANGLE -> "<"
  | RANGLE -> ">"
  | SINGLE -> "S"
  | PI -> "Π"
  | SIGMA -> "Σ"
  | NU -> "ν"
  | OPEN -> "open"
  | COLON -> ":"
  | LBRACE -> "{"
  | RBRACE -> "}"
  | LBRACKET -> "["
  | RBRACKET -> "]"
  | EQ -> "="
  | FORALL -> "∀"
  | EXISTS -> "∃"
  | ARROW -> "→"
  | EXPORT -> "export"
  | IMPORT -> "import"
  | EOF -> "\n"
