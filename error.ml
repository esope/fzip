(* categories of errors *)
type t = int
let lexing = 1
let parsing = 2

let raise_error n startpos endpos msg =
  let open Lexing in
  Printf.eprintf "File \"%s\", line %i, characters %i-%i:\n%!"
    startpos.pos_fname startpos.pos_lnum
    (startpos.pos_cnum - startpos.pos_bol)
    (endpos.pos_cnum - endpos.pos_bol);
  Printf.eprintf "%s\n%!" msg ;
  exit n
