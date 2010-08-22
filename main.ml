open Ast
open Ast_utils

let () =
  let typ = Parser.Channel.parse_typ stdin in
  Printf.printf "%a\n%!" (fun _ -> Print.typ) typ
