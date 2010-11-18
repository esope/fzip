(* categories of errors *)
type t = int * string

module Tbl = Hashtbl.Make(MyInt)
let tbl = Tbl.create 16
let register_id: int -> string -> unit = Tbl.add tbl

let id = ref 0
let next_id () = incr id; !id
let make_id s =
  let i = next_id () in
  register_id i s ;
  (i, s)

let lexing  = make_id "Lexing"
let parsing = make_id "Parsing"
let syntax  = make_id "Syntax"
let type_wf = make_id "Type wellformedness"
let kind_wf = make_id "Kind wellformedness"
let term_wf = make_id "Term wellformedness"
let prog_wf = make_id "Program wellformedness"
let subtype = make_id "Subtyping"
let subkind = make_id "Subkinding"
let zip = make_id "Zip"
let purity = make_id "Purity"
let misused_typ_var = make_id "Misuse of a type variable"
let escaping_typ_var = make_id "Scope"
let not_implemented = make_id "Not implemented"

let list_errors () =
  Tbl.fold (fun i s l -> (i,s) :: l) tbl []

exception ERROR of t * Lexing.position * Lexing.position * string

let raise_error t startpos endpos msg =
  raise (ERROR(t, startpos, endpos, msg))

let handle_error_and_exit f =
  try f ()
  with ERROR ((n, cat), startpos, endpos, msg) ->
    let open Lexing in
    Printf.eprintf "File \"%s\", line %i, characters %i-%i:\n%!"
      startpos.pos_fname startpos.pos_lnum startpos.pos_cnum
      (endpos.pos_cnum + (endpos.pos_bol - startpos.pos_bol));
    Printf.eprintf "%s error:\n%s\n%!" cat msg ;
    exit n
