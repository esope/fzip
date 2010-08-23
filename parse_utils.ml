let convert_parser parser =
  MenhirLib.Convert.Simplified.traditional2revised
    parser

let typ_expr_parser = convert_parser Parsers.typ_expr

let kind_expr_parser = convert_parser Parsers.kind_expr

module String =  struct

  let raw_parse_typ s =
    let lexbuf = Ulexing.from_utf8_string s in
    typ_expr_parser (fun () -> Lexer.token "from_string" lexbuf)

  let parse_typ s =
    Ast_utils.Encode.typ (raw_parse_typ s)

  let raw_parse_kind s =
    let lexbuf = Ulexing.from_utf8_string s in
    kind_expr_parser (fun () -> Lexer.token "from_string" lexbuf)

  let parse_kind s =
    Ast_utils.Encode.kind (raw_parse_kind s)

end

module Channel =  struct

  let raw_parse_typ chan =
    let lexbuf = Ulexing.from_utf8_channel chan in
    typ_expr_parser (fun () -> Lexer.token "from_string" lexbuf)

  let parse_typ chan =
    Ast_utils.Encode.typ (raw_parse_typ chan)

  let raw_parse_kind chan =
    let lexbuf = Ulexing.from_utf8_channel chan in
    kind_expr_parser (fun () -> Lexer.token "from_string" lexbuf)

  let parse_kind chan =
    Ast_utils.Encode.kind (raw_parse_kind chan)
end
