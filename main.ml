let run () =
  let (input, name) =
    match Array.length Sys.argv with
    | 1 -> (stdin, "<stdin>")
    | k when k > 1 -> (open_in Sys.argv.(1), Sys.argv.(1))
    | _ -> assert false
  in
  let term = Parser_utils.Channel.Term.parse input name in
  let (_, typ) = Wfterm.wfterm Env.empty term in
  Ast_utils.PPrint.Typ.channel stdout typ ; print_newline ()

let () = Error.handle_error_and_exit run
