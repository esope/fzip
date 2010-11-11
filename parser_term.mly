%{

open Ast.Raw

%}

%start<(Ast.Raw.typ Ast.Raw.kind, Ast.Raw.typ) Ast.Raw.term> main_term_expr

%%

term_binding(typ):
| LPAR x=ID COLON tau=typ RPAR
    { (x, tau) }

term_fields(kind,typ):
| 
    { (Label.AList.empty, Label.Set.empty) }
| VAL lab=ID EQ t=term(kind,typ) f=term_fields(kind,typ)
    { let (fields, labels) = f in
    if Label.Set.mem lab labels
    then Error.raise_error Error.term_wf $startpos(lab) $endpos(lab)
        (Printf.sprintf "Duplicate record label: %s." lab)
    else (Label.AList.add lab t fields, Label.Set.add lab labels) }

undelimited_term(kind,typ):
| LAMBDA b=term_binding(typ) t=term(kind,typ)
    { mkTeLam_binding b t $startpos $endpos }
| UPLAMBDA b=typ_binding(kind) t=term(kind,typ)
| LAMBDA b=typ_binding(kind) t=term(kind,typ)
  (* we allow the use of λ of Λ for type generalization *)
    { mkTeGen_binding b t $startpos $endpos }

delimited_term(kind,typ):
| LPAR t=term(kind,typ) RPAR { locate t.Location.content $startpos $endpos }
| x=ID { locate (TeVar x) $startpos $endpos }
| t1=delimited_term(kind,typ) t2=delimited_term(kind,typ)             %prec APP
    { locate (TeApp(t1, t2)) $startpos $endpos }
| LBRACE f=term_fields(kind,typ) RBRACE
    { locate (TeRecord (fst f)) $startpos $endpos }
| t=delimited_term(kind,typ) DOT x=ID
    { locate (TeProj(t, locate x ($startpos(x)) ($endpos(x)))) $startpos $endpos }
| t=delimited_term(kind,typ) LBRACKET tau=typ RBRACKET
    { locate (TeInst(t, tau)) $startpos $endpos }
| LPAR t=term(kind,typ) COLON tau=typ RPAR
    { locate (TeAnnot(t, tau)) $startpos $endpos }

term(kind,typ):
| t=undelimited_term(kind,typ) | t=delimited_term(kind,typ)
    { t }

term_expr(kind,typ):
| t=term(kind,typ) EOF { t }

main_term_expr:
| t=term_expr(kind,typ) { t }
