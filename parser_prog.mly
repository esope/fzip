%%

import_req(kind,typ):
| VAL x=ID y=option(preceded(AS,ID)) COLON t=typ
    { let var = match y with
    | None -> locate x $startpos(x) $endpos(x)
    | Some y -> locate y $startpos(y) $endpos(y)
    in RequireVal(var, t) }
| TYPE x=ID y=option(preceded(AS,ID)) DBLCOLON k=kind
    { let var = match y with
    | None -> locate x $startpos(x) $endpos(x)
    | Some y -> locate y $startpos(y) $endpos(y)
    in RequireTyp(var, locate k $startpos(k) $endpos(k))
    }

export_req(kind,typ):
| TYPE x=ID y=option(preceded(AS,ID)) DBLCOLON k=kind
    { let var = match y with
    | None -> locate x $startpos(x) $endpos(x)
    | Some y -> locate y $startpos(y) $endpos(y)
    in ExportTyp(var, locate k $startpos(k) $endpos(k))
    }

req(kind,typ):
| EXPORT LBRACE l=list(export_req(kind,typ)) RBRACE
    { List.rev l }
| IMPORT LBRACE l=list(import_req(kind,typ)) RBRACE
    { List.rev l }

header(kind,typ):
| l=list(req(kind,typ))
  { List.flatten (List.rev l) }

header_expr(kind,typ):
| h=header(kind,typ) EOF { h }

main_header_expr:
| h=header_expr(kind,typ) { h }

prog:
| h=header(kind,typ) t=main_term_expr { { reqs = h ; code = t } }
