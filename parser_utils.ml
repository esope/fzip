let convert_parser parser =
  MenhirLib.Convert.Simplified.traditional2revised
    parser

let typ_expr_parser = convert_parser Parser.typ_expr

let kind_expr_parser = convert_parser Parser.kind_expr

let term_expr_parser = convert_parser Parser.main_term_expr

module String =  struct

  let raw_parse_typ s =
    let lexbuf = Ulexing.from_utf8_string s in
    typ_expr_parser (fun () -> Lexer.token "from_string" lexbuf)

  let parse_typ s =
    Ast_utils.Encode.Typ.typ (raw_parse_typ s)

  let raw_parse_kind s =
    let lexbuf = Ulexing.from_utf8_string s in
    kind_expr_parser (fun () -> Lexer.token "from_string" lexbuf)

  let parse_kind s =
    Ast_utils.Encode.Typ.kind (raw_parse_kind s)

  let raw_parse_term s =
    let lexbuf = Ulexing.from_utf8_string s in
    term_expr_parser (fun () -> Lexer.token "from_string" lexbuf)

  let parse_term s =
    Ast_utils.Encode.Term.term (raw_parse_term s)

end

module Channel =  struct

  let raw_parse_typ chan =
    let lexbuf = Ulexing.from_utf8_channel chan in
    typ_expr_parser (fun () -> Lexer.token "from_chan" lexbuf)

  let parse_typ chan =
    Ast_utils.Encode.Typ.typ (raw_parse_typ chan)

  let raw_parse_kind chan =
    let lexbuf = Ulexing.from_utf8_channel chan in
    kind_expr_parser (fun () -> Lexer.token "from_chan" lexbuf)

  let parse_kind chan =
    Ast_utils.Encode.Typ.kind (raw_parse_kind chan)

  let raw_parse_term s =
    let lexbuf = Ulexing.from_utf8_channel s in
    term_expr_parser (fun () -> Lexer.token "from_chan" lexbuf)

  let parse_term s =
    Ast_utils.Encode.Term.term (raw_parse_term s)

end
