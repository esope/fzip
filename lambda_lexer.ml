open Lambda_parser
open Ulexing

exception Lexing_error of string * Lexing.position

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

let lnum = ref 0
let bol = ref 0
let break_line () =
  incr lnum ; incr bol
let skip_length lexbuf =
  bol := lexeme_length lexbuf + !bol
let locate file lexbuf token =
  let startpos =
    { Lexing.pos_fname = file ;
      Lexing.pos_lnum = !lnum ;
      Lexing.pos_bol = !bol ;
      Lexing.pos_cnum = lexeme_start lexbuf }
  and endpos =
    { Lexing.pos_fname = file ;
      Lexing.pos_lnum = !lnum ;
      Lexing.pos_bol = !bol ;
      Lexing.pos_cnum = lexeme_end lexbuf }
  in
  skip_length lexbuf ;
  (token, startpos, endpos)
let pos_at_point file lexbuf =
    { Lexing.pos_fname = file ;
      Lexing.pos_lnum = !lnum ;
      Lexing.pos_bol = !bol ;
      Lexing.pos_cnum = lexeme_start lexbuf }

let rec token (file:string) = lexer
| whitespace -> skip_length lexbuf ; token file lexbuf
| linebreak -> break_line () ; token file lexbuf
| "=>" | 8658 (* ⇒ *) -> locate file lexbuf DBLARROW
| "*" | 8902 (* ⋆ *) -> locate file lexbuf STAR
| "fun" | 955 (* λ *) -> locate file lexbuf LAMBDA
| "::" -> locate file lexbuf DBLCOLON
| "(" -> locate file lexbuf LPAR
| ")" -> locate file lexbuf RPAR
| "." -> locate file lexbuf DOT
| "," -> locate file lexbuf COMMA
| "<" -> locate file lexbuf LANGLE
| ">" -> locate file lexbuf RANGLE
| 215 (* × *) -> locate file lexbuf TIMES
| "Pi" | 928 (* Π *) -> locate file lexbuf PI
| "Sigma" |  931 (* Σ *) -> locate file lexbuf SIGMA
| "S" -> locate file lexbuf SINGLE
| eof -> locate file lexbuf EOF
| id -> locate file lexbuf (ID (utf8_lexeme lexbuf))
| _ -> raise (Lexing_error (utf8_lexeme lexbuf, pos_at_point file lexbuf))

let string_of_token = function
  | ID x -> x
  | LAMBDA -> "λ"
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
  | EOF -> "\n"
