%{

open Ast.Raw

%}

%start<(Ast.Raw.typ Ast.Raw.kind, Ast.Raw.typ) Ast.Raw.term> main_term_expr

%%

term_binding(typ):
| LPAR x=ID COLON t=typ RPAR
    { ($startpos, x, t) }

mixed_binding(typ,kind):
| b=term_binding(typ)
    { let (startpos, x, t) = b in TeBind (startpos, x, t) }
| b=typ_binding(kind)
    { let (startpos, a, k) = b in TyBind (startpos, a, k) }

mixed_bindings(typ,kind):
| l=nonempty_list(mixed_binding(typ,kind))
    { l }

term_fields(kind,typ):
| 
    { (Label.AList.empty, Label.Set.empty) }
| VAL lab=ID params=list(mixed_binding(typ,kind))
    EQ t=term(kind,typ) f=term_fields(kind,typ)
    { let (fields, labels) = f in
    if Label.Set.mem lab labels
    then Error.raise_error Error.term_wf $startpos(lab) $endpos(lab)
        (Printf.sprintf "Duplicate record label: %s." lab)
    else (Label.AList.add lab (mkTe_mixed_bindings params t $endpos(t)) fields,
          Label.Set.add lab labels) }

undelimited_term(kind,typ):
| LAMBDA b=mixed_bindings(typ,kind) ARROW t=term(kind,typ)
    { relocate (mkTe_mixed_bindings b t $endpos) $startpos $endpos }
| UPLAMBDA b=typ_bindings(kind) ARROW t=term(kind,typ)
  (* we allow the use of λ of Λ for type generalization *)
    { relocate (mkTeGen_bindings b t $endpos) $startpos $endpos }
| LET x=ID EQ t1=term(kind,typ) IN t2=term(kind,typ)
    { locate (TeLet (x, t1, t2)) $startpos $endpos }
| LET x=ID COLON tau=typ EQ t1=term(kind,typ) IN t2=term(kind,typ)
    { let t1' = locate (TeAnnot(t1, tau)) $startpos(tau) $endpos(t1) in
    locate (TeLet (x, t1', t2)) $startpos $endpos }
| OPEN LBRACKET x=ID RBRACKET t=delimited_term(kind,typ)
    { locate (TeOpen(locate x $startpos(x) $endpos(x), t)) $startpos $endpos }
| NU LPAR x=ID DBLCOLON k=kind RPAR t=term(kind,typ)
    { locate (TeNu(x, locate k $startpos(k) $endpos(k), t)) $startpos $endpos }
| SIGMA LBRACE x=ID RBRACE
    LPAR y=ID DBLCOLON k=kind EQ tau=typ RPAR t=term(kind,typ)
    { locate
        (TeSigma(locate x $startpos(x) $endpos(x),
                 y, locate k $startpos(k) $endpos(k), tau, t))
        $startpos $endpos }


delimited_term(kind,typ):
| LPAR t=term(kind,typ) RPAR { relocate t $startpos $endpos }
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
