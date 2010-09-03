open Ast
open Ast_utils

let () =
  let (input, name) =
    match Array.length Sys.argv with
    | 1 -> (stdin, "<stdin>")
    | k when k > 1 -> (open_in Sys.argv.(1), Sys.argv.(1))
    | _ -> assert false
  in
  let term = Parser_utils.Channel.parse_term input name in
  let typ = Wfterm.wfterm Env.empty term in
  PPrint.Typ.channel stdout typ ; print_newline ()
