%{

%}

%start <Ast.Raw.typ> typ_expr
%start <Ast.Raw.typ Ast.Raw.kind> kind_expr

%%

%public %inline typ_binding(kind):
| LPAR x=ID DBLCOLON k=kind RPAR
    { (x, Location.locate k $startpos(k) $endpos(k)) }

kind_fields:
| 
  { Label.AList.empty }
| TYPE lab=ID AS a=ID DBLCOLON k=kind f=kind_fields
    { (lab, (a, k)) :: f }
| TYPE lab=ID DBLCOLON k=kind f=kind_fields
    { let a = Ast.Typ.Var.to_string (Ast.Typ.Var.fresh ()) in
    (lab, (a, k)) :: f }

undelimited_kind:
| PI b=typ_binding(kind) k=kind { mkPi_binding b k }

delimited_kind:
| STAR { Base }
| k1=delimited_kind DBLARROW k2=delimited_kind { mkArrow k1 k2 }
| SINGLE LPAR t=typ RPAR { Single (t, Base) }
| SINGLE LPAR t=typ DBLCOLON k=kind RPAR { Single (t, k) }
| LANGLE f=kind_fields RANGLE { Sigma f }
| LPAR k=kind RPAR { k }

%public kind:
| k=undelimited_kind | k=delimited_kind
    { k }

kind_expr:
| k=kind EOF { k }

typ_base_fields:
| 
    { Label.Map.empty }
| VAL lab=ID COLON t=typ f=typ_base_fields
    { if Label.Map.mem lab f
    then Error.raise_error Error.term_wf $startpos(lab) $endpos(lab)
        (Printf.sprintf "Duplicate record label: %s." lab)
    else Label.Map.add lab t f }

typ_fields:
| 
    { Label.Map.empty }
| TYPE lab=ID EQ t=typ f=typ_fields
    { if Label.Map.mem lab f
    then Error.raise_error Error.term_wf $startpos(lab) $endpos(lab)
        (Printf.sprintf "Duplicate record label: %s." lab)
    else Label.Map.add lab t f }

undelimited_typ:
| LAMBDA b=typ_binding(kind) t=typ
    { mkLam_binding b t $startpos $endpos }
| FORALL b=typ_binding(kind) t=typ
    { mkForall_binding b t $startpos $endpos }
| EXISTS b=typ_binding(kind) t=typ
    { mkExists_binding b t $startpos $endpos }

delimited_typ:
| LPAR t=typ RPAR { locate t.Location.content $startpos $endpos }
| x=ID { locate (Var x) $startpos $endpos }
| t1=delimited_typ t2=delimited_typ                 %prec APP
    { locate (App(t1, t2)) $startpos $endpos }
| LANGLE f=typ_fields RANGLE
    { locate (Record f) $startpos $endpos }
| t=delimited_typ DOT x=ID
    { locate (Proj(t, locate x ($startpos(x)) ($endpos(x)))) $startpos $endpos }
| LBRACE f=typ_base_fields RBRACE
    {locate (BaseRecord f) $startpos $endpos }
| t1=delimited_typ ARROW t2=delimited_typ
    {locate (BaseArrow(t1, t2)) $startpos $endpos }

%public typ:
| t=undelimited_typ | t=delimited_typ
    { t }

typ_expr:
| t=typ EOF { t }

%%

