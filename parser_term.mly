%{

open Ast.Raw

%}

%start<(Ast.Raw.typ Ast.Raw.kind, Ast.Raw.typ) Ast.Raw.term> main_term_expr

%%

term_binding(typ):
| LPAR x=ID COLON tau=typ RPAR
    { (x, tau) }

term_fields(kind,typ):
| l = separated_list(SEMICOLON, separated_pair(ID, EQ, term(kind,typ)))
    { l }

undelimited_term(kind,typ):
| LAMBDA b=term_binding(typ) t=term(kind,typ)
    { mkTeLam_binding b t $startpos $endpos }
| UPLAMBDA b=typ_binding(kind) t=term(kind,typ)
    { mkTeGen_binding b t $startpos $endpos }

delimited_term(kind,typ):
| LPAR t=term(kind,typ) RPAR { t }
| x=ID { locate (TeVar x) $startpos $endpos }
| t1=delimited_term(kind,typ) t2=delimited_term(kind,typ)             %prec APP
    { locate (TeApp(t1, t2)) $startpos $endpos }
| LBRACE t1=delimited_term(kind,typ) COMMA t2=term(kind,typ) RBRACE
    { locate (TePair(t1, t2)) $startpos $endpos }
| t=delimited_term(kind,typ) DOT x=ID
    { locate (TeProj(t, x)) $startpos $endpos }
| t=delimited_term(kind,typ) LBRACKET tau=typ RBRACKET
    { locate (TeInst(t, tau)) $startpos $endpos }

term(kind,typ):
| t=undelimited_term(kind,typ) | t=delimited_term(kind,typ)
    { t }

term_expr(kind,typ):
| t=term(kind,typ) EOF { t }

main_term_expr:
| t=term_expr(kind,typ) { t }
