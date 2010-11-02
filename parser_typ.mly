%{

%}

%start <Ast.Raw.typ> typ_expr
%start <Ast.Raw.typ Ast.Raw.kind> kind_expr

%%

%public %inline typ_binding(kind):
| LPAR x=ID DBLCOLON k=kind RPAR
    { (x, Location.locate k $startpos(k) $endpos(k)) }

undelimited_kind:
| PI b=typ_binding(kind) k=kind { mkPi_binding b k }
| SIGMA b=typ_binding(kind) k=kind { mkSigma_binding b k }

delimited_kind:
| STAR { Base }
| k1=delimited_kind DBLARROW k2=delimited_kind { Arrow(k1, k2) }
| k1=delimited_kind TIMES k2=delimited_kind { Prod(k1, k2) }
| SINGLE LPAR t=typ RPAR { Single t }
| LPAR k=kind RPAR { k }

%public kind:
| k=undelimited_kind | k=delimited_kind
    { k }

kind_expr:
| k=kind EOF { k }

undelimited_typ:
| LAMBDA b=typ_binding(kind) t=typ
    { mkLam_binding b t $startpos $endpos }
| FORALL b=typ_binding(kind) t=typ
    { mkForall_binding b t $startpos $endpos }

delimited_typ:
| LPAR t=typ RPAR { t }
| x=ID { locate (Var x) $startpos $endpos }
| t1=delimited_typ t2=delimited_typ                 %prec APP
    { locate (App(t1, t2)) $startpos $endpos }
| LANGLE t1=delimited_typ COMMA t2=typ RANGLE
    { locate (Pair(t1, t2)) $startpos $endpos }
| t=delimited_typ DOT x=ID
    { locate (Proj(t, locate x ($startpos(x)) ($endpos(x)))) $startpos $endpos }
| LBRACE t1=delimited_typ SEMICOLON t2=typ RBRACE
    {locate (BaseProd(t1, t2)) $startpos $endpos }
| t1=delimited_typ ARROW t2=delimited_typ
    {locate (BaseArrow(t1, t2)) $startpos $endpos }

%public typ:
| t=undelimited_typ | t=delimited_typ
    { t }

typ_expr:
| t=typ EOF { t }

%%

