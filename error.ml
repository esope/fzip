(* categories of errors *)
type t = int * string

let id = ref 0
let next_id () = incr id; !id
let make_id s = (next_id (), s)

let lexing  = make_id "Lexing"
let parsing = make_id "Parsing"
let syntax  = make_id "Syntax"
let type_wf  = make_id "Type wellformedness"
let kind_wf  = make_id "Kind wellformedness"

let raise_error (n, cat) startpos endpos msg =
  let open Lexing in
  Printf.eprintf "File \"%s\", line %i, characters %i-%i:\n%!"
    startpos.pos_fname startpos.pos_lnum
    (startpos.pos_cnum - startpos.pos_bol)
    (endpos.pos_cnum - endpos.pos_bol);
  Printf.eprintf "%s error:\n%s\n%!" cat msg ;
  exit n
