let parser_error_handle parser next_token file =
    try parser next_token
    with Parser.Error ->
      Error.raise_error Error.parsing
        !Lexer.current_start !Lexer.current_end
        (Printf.sprintf "Unexpected token: '%s'."
           (Lexer.string_of_token !Lexer.current_token))

let convert_parser parser =
  MenhirLib.Convert.Simplified.traditional2revised
    parser

let typ_expr_parser = convert_parser Parser.typ_expr

let kind_expr_parser = convert_parser Parser.kind_expr

let term_expr_parser = convert_parser Parser.main_term_expr

module String =  struct

  let raw_parse_typ s =
    let lexbuf = Ulexing.from_utf8_string s in
    let file = "<string>" in
    parser_error_handle
    typ_expr_parser (fun () -> Lexer.token file lexbuf) file

  let parse_typ s =
    Ast_utils.Encode.Typ.typ (raw_parse_typ s)

  let raw_parse_kind s =
    let lexbuf = Ulexing.from_utf8_string s in
    let file = "<string>" in
    parser_error_handle
    kind_expr_parser (fun () -> Lexer.token file lexbuf) file

  let parse_kind s =
    Ast_utils.Encode.Typ.kind (raw_parse_kind s)

  let raw_parse_term s =
    let lexbuf = Ulexing.from_utf8_string s in
    let file = "<string>" in
    parser_error_handle
    term_expr_parser (fun () -> Lexer.token file lexbuf) file

  let parse_term s =
    Ast_utils.Encode.Term.term (raw_parse_term s)

end

module Channel =  struct

  let raw_parse_typ chan file =
    let lexbuf = Ulexing.from_utf8_channel chan in
    parser_error_handle
      typ_expr_parser (fun () -> Lexer.token file lexbuf) file

  let parse_typ chan file =
    Ast_utils.Encode.Typ.typ (raw_parse_typ chan file)

  let raw_parse_kind chan file =
    let lexbuf = Ulexing.from_utf8_channel chan in
    parser_error_handle
      kind_expr_parser (fun () -> Lexer.token file lexbuf) file

  let parse_kind chan file =
    Ast_utils.Encode.Typ.kind (raw_parse_kind chan file)

  let raw_parse_term chan file =
    let lexbuf = Ulexing.from_utf8_channel chan in
    parser_error_handle
      term_expr_parser (fun () -> Lexer.token file lexbuf) file

  let parse_term chan file =
    Ast_utils.Encode.Term.term (raw_parse_term chan file)

end
