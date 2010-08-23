(* categories of errors *)
let lexing = 1
let parsing = 2

open Lexing
let raise_error n startpos endpos msg =
  Printf.eprintf "File \"%s\", line %i, characters %i-%i:\n%!"
    startpos.pos_fname startpos.pos_lnum
    (startpos.pos_cnum - startpos.pos_bol)
    (endpos.pos_cnum - endpos.pos_bol);
  Printf.eprintf "%s\n%!" msg ;
  exit n
