%{

open Ast.Raw

%}

%start<(Ast.Raw.typ Ast.Raw.kind, Ast.Raw.typ) Ast.Raw.term> main_term_expr

%%

mixed_binding(typ,kind):
| LPAR x=ID COLON t=typ RPAR
    { TeBind ($startpos, x, t) }
| LPAR a=ID DBLCOLON k=kind RPAR
    { TyBind ($startpos, a, locate k $startpos(k) $endpos(k)) }

mixed_bindings(typ,kind):
| l=nonempty_list(mixed_binding(typ,kind))
    { l }

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
| LAMBDA b=mixed_bindings(typ,kind) ARROW t=term(kind,typ)
    { { (mkTe_mixed_bindings b t $endpos) with Location.startpos = $startpos } }
| UPLAMBDA b=typ_binding(kind) ARROW t=term(kind,typ)
  (* we allow the use of λ of Λ for type generalization *)
    { mkTeGen_binding b t $startpos $endpos }
| LET x=ID EQ t1=term(kind,typ) IN t2=term(kind,typ)
    { locate (TeLet (x, t1, t2)) $startpos $endpos }
| LET x=ID COLON tau=typ EQ t1=term(kind,typ) IN t2=term(kind,typ)
    { let t1' = locate (TeAnnot(t1, tau)) $startpos(tau) $endpos(t1) in
    locate (TeLet (x, t1', t2)) $startpos $endpos }

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
