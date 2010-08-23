open Ast
open Ast_utils

let () =
  let input =
    match Array.length Sys.argv with
    | 1 -> stdin
    | k when k > 1 -> open_in Sys.argv.(1)
    | _ -> assert false
  in
  let term = Parser_utils.Channel.parse_term input in
  let typ = Wfterm.wfterm Env.empty term in
  Printf.printf "%a\n%!" (fun _ -> Print.typ) typ
