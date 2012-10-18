let parser_error_handle parser next_token =
    try parser next_token
    with Parser.Error ->
      let current_start = Lexer.get_current_start ()
      and current_end = Lexer.get_current_end ()
      and current_token = Lexer.get_current_token () in
      Error.raise_error Error.parsing
        current_start current_end
        (Printf.sprintf "Unexpected token: '%s'."
           (Lexer.string_of_token current_token))

let convert_parser parser =
  MenhirLib.Convert.Simplified.traditional2revised
    parser

let typ_expr_parser = convert_parser Parser.typ_expr

let kind_expr_parser = convert_parser Parser.kind_expr

let term_expr_parser = convert_parser Parser.main_term_expr

let prog_parser = convert_parser Parser.prog

module String =  struct
  module Raw = struct
    module Typ = struct
      let parse s =
        let lexbuf = Ulexing.from_utf8_string s in
        let file = "<string>" in
        parser_error_handle
          typ_expr_parser (fun () -> Lexer.token file lexbuf)
    end

    module Kind = struct
      let parse s =
        let lexbuf = Ulexing.from_utf8_string s in
        let file = "<string>" in
        parser_error_handle
          kind_expr_parser (fun () -> Lexer.token file lexbuf)
    end

    module Term = struct
      let parse s =
        let lexbuf = Ulexing.from_utf8_string s in
        let file = "<string>" in
        parser_error_handle
          term_expr_parser (fun () -> Lexer.token file lexbuf)
    end

    module Prog = struct
      let parse s =
        let lexbuf = Ulexing.from_utf8_string s in
        let file = "<string>" in
        parser_error_handle
          prog_parser (fun () -> Lexer.token file lexbuf)
    end
  end

  module Typ = struct
    let parse s =
      Ast_utils.Encode.Typ.typ (Raw.Typ.parse s)
  end

  module Kind = struct
    let parse s =
      Ast_utils.Encode.Typ.kind (Raw.Kind.parse s)
  end

  module Term = struct
    let parse s =
      Ast_utils.Encode.Term.term (Raw.Term.parse s)
  end

  module Prog = struct
    let parse s =
      Ast_utils.Encode.Prog.prog (Raw.Prog.parse s)
  end

end

module Channel =  struct
  module Raw = struct
    module Typ = struct
      let parse chan file =
        let lexbuf = Ulexing.from_utf8_channel chan in
        parser_error_handle
          typ_expr_parser (fun () -> Lexer.token file lexbuf)
    end

    module Kind = struct
      let parse chan file =
        let lexbuf = Ulexing.from_utf8_channel chan in
        parser_error_handle
          kind_expr_parser (fun () -> Lexer.token file lexbuf)
    end

    module Term = struct
      let parse chan file =
        let lexbuf = Ulexing.from_utf8_channel chan in
        parser_error_handle
          term_expr_parser (fun () -> Lexer.token file lexbuf)
    end

    module Prog = struct
      let parse chan file =
        let lexbuf = Ulexing.from_utf8_channel chan in
        parser_error_handle
          prog_parser (fun () -> Lexer.token file lexbuf)
    end
  end

  module Typ = struct
    let parse chan file =
      Ast_utils.Encode.Typ.typ (Raw.Typ.parse chan file)
  end

  module Kind = struct
    let parse chan file =
      Ast_utils.Encode.Typ.kind (Raw.Kind.parse chan file)
  end

  module Term = struct
    let parse chan file =
      Ast_utils.Encode.Term.term (Raw.Term.parse chan file)
  end

  module Prog = struct
    let parse chan file =
      Ast_utils.Encode.Prog.prog (Raw.Prog.parse chan file)
  end

end
