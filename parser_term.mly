%{

open Ast.Raw

%}

%start<(Ast.Raw.typ Ast.Raw.kind, Ast.Raw.typ) Ast.Raw.term> main_term_expr
%start<Ast.Raw.reqs> main_header_expr
%start<Ast.Raw.prog> prog

%%

term_binding(typ):
| LPAR x=ID COLON t=typ RPAR
    { ($startpos, locate x $startpos(x) $endpos(x), t) }

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
    tau=option(preceded(COLON,typ))
    EQ t=term(kind,typ) f=term_fields(kind,typ)
    { let (fields, labels) = f in
    if Label.Set.mem lab labels
    then Error.raise_error Error.term_wf $startpos(lab) $endpos(lab)
        (Printf.sprintf "Duplicate record label: %s." lab)
    else
      let t = match tau with
      | Some tau -> locate (TeAnnot(t, tau)) $startpos(tau) $endpos(t)
      | None -> t
      in
      (Label.AList.add lab (mkTe_mixed_bindings params t $endpos(t)) fields,
          Label.Set.add lab labels) }
| VAL REC lab=ID b=list(mixed_binding(typ,kind)) COLON tau=typ
    EQ t=term(kind,typ) f=term_fields(kind,typ)
    { let (fields, labels) = f in
    if Label.Set.mem lab labels
    then Error.raise_error Error.term_wf $startpos(lab) $endpos(lab)
        (Printf.sprintf "Duplicate record label: %s." lab)
    else
      let tau_fix = mkTy_mixed_bindings b tau $endpos(tau) in
      let t_tau = locate (TeAnnot(t, tau)) $startpos(tau) $endpos(t) in
      let t_with_bindings =
        mkTe_mixed_bindings b t_tau t_tau.Location.endpos in
      let t_fix =
        locate
          (TeFix(locate lab $startpos(lab) $endpos(lab),
                 tau_fix, t_with_bindings))
          $startpos(lab) t_with_bindings.Location.endpos in
      (Label.AList.add lab t_fix fields,
       Label.Set.add lab labels)
    }


simple_term(kind,typ):
| x=ID
    { locate (TeVar x) $startpos $endpos }
| LBRACE f=term_fields(kind,typ) RBRACE
    { locate (TeRecord (fst f)) $startpos $endpos }
| t=simple_term(kind,typ) DOT x=ID
    { locate (TeProj(t, locate x ($startpos(x)) ($endpos(x)))) $startpos $endpos }
| LPAR t=term(kind,typ) COLON tau=typ RPAR
    { locate (TeAnnot(t, tau)) $startpos $endpos }
| LPAR t=term(kind,typ) RPAR
    { relocate t $startpos $endpos }

open_term(kind,typ):
| OPEN LBRACKET x=ID RBRACKET t=open_term(kind,typ)
    { locate (TeOpen(locate x $startpos(x) $endpos(x), t)) $startpos $endpos }
| t=simple_term(kind,typ)
    { t }

app_term(kind,typ):
| t1=app_term(kind,typ) t2=simple_term(kind,typ)
    { locate (TeApp(t1, t2)) $startpos $endpos }
| t=app_term(kind,typ) LBRACKET tau=typ RBRACKET
    { locate (TeInst(t, tau)) $startpos $endpos }
| t=open_term(kind,typ)
    { t }

term(kind,typ):
| LAMBDA b=mixed_bindings(typ,kind) ARROW t=term(kind,typ)
    { relocate (mkTe_mixed_bindings b t $endpos) $startpos $endpos }
| UPLAMBDA b=typ_bindings(kind) ARROW t=term(kind,typ)
  (* we allow the use of λ of Λ for type generalization *)
    { relocate (mkTeGen_bindings b t $endpos) $startpos $endpos }
| LET x=ID b=list(mixed_binding(typ,kind)) tau=option(preceded(COLON,typ))
    EQ t1=term(kind,typ) IN t2=term(kind,typ)
    { let t1 = match tau with
    | Some tau ->
        locate (TeAnnot(t1, tau)) $startpos(tau) $endpos(t1)
    | None -> t1
    in let t1 = mkTe_mixed_bindings b t1 $endpos(t1) in
    locate
      (TeLet (locate x $startpos(x) $endpos(x), t1, t2)) $startpos $endpos }
| LET REC x=ID b=list(mixed_binding(typ,kind)) COLON tau=typ
    EQ t1=term(kind,typ) IN t2=term(kind,typ)
    { let tau_fix = mkTy_mixed_bindings b tau $endpos(tau) in
      let t1_tau = locate (TeAnnot(t1, tau)) $startpos(tau) $endpos(t1) in
      let t1_with_bindings =
        mkTe_mixed_bindings b t1_tau t1_tau.Location.endpos in
      let t1_fix =
        locate
          (TeFix(locate x $startpos(x) $endpos(x), tau_fix, t1_with_bindings))
          $startpos(x) t1_with_bindings.Location.endpos in
      locate
        (TeLet (locate x $startpos(x) $endpos(x), t1_fix, t2))
        $startpos $endpos }
| NU LPAR x=ID DBLCOLON k=kind RPAR t=term(kind,typ)
    { locate
        (TeNu (locate x $startpos(x) $endpos(x),
               locate k $startpos(k) $endpos(k), t))
        $startpos $endpos }
| EXISTS LPAR x=ID DBLCOLON k=kind RPAR t=term(kind,typ)
    { locate
        (TeEx (locate x $startpos(x) $endpos(x),
               locate k $startpos(k) $endpos(k), t))
        $startpos $endpos }
| EXISTS LPAR x=ID DBLCOLON k=kind EQ tau=typ RPAR t=term(kind,typ)
    { let x = locate x $startpos(x) $endpos(x)
    and k = locate k $startpos(k) $endpos(k)
    and y = dummy_locate (Ast.Typ.Var.to_string (Ast.Typ.Var.fresh ())) in
    locate
      (TeEx (y, k,
             locate (TeSigma (y, x, k, tau, t)) $startpos $endpos))
      $startpos $endpos }
| SIGMA LBRACKET x=ID RBRACKET
    LPAR y=ID DBLCOLON k=kind EQ tau=typ RPAR t=term(kind,typ)
    { locate
        (TeSigma(locate x $startpos(x) $endpos(x),
                 locate y $startpos(y) $endpos(y),
                 locate k $startpos(k) $endpos(k), tau, t))
        $startpos $endpos }
| LET TYPE x=ID b=list(typ_binding(kind)) DBLCOLON k=kind
    EQ tau=typ IN t=term(kind,typ)
    { let tau = mkLam_bindings b tau $endpos(tau)
    and k = mkPi_bindings b k
    and x = locate x $startpos(x) $endpos(x)
    and y = dummy_locate (Ast.Typ.Var.to_string (Ast.Typ.Var.fresh ())) in
    let single_tau_k = locate (Single(tau, k)) $startpos(b) $endpos(k) in
    let t' = locate (TeSigma(y, x, single_tau_k, tau, t)) $startpos $endpos in
    locate (TeNu (y, single_tau_k, t')) $startpos $endpos }
| t=app_term(kind,typ)
    { t }

term_expr(kind,typ):
| t=term(kind,typ) EOF { t }

main_term_expr:
| t=term_expr(kind,typ) { t }
