%{

open Ast.Raw
let locate = Location.locate

let mkPi_binding (x,k) k' = RPi(x, k, k')

let mkSigma_binding (x,k) k' = RSigma(x, k, k')

let mkLam_binding (x,k) t = locate (RLam(x, k, t))

%}

%token EOF

%token STAR DBLARROW

%token LAMBDA LPAR RPAR DBLCOLON APP
%token LANGLE RANGLE COMMA DOT TIMES
%token SINGLE
%token PI SIGMA
%token <string> ID

%nonassoc LPAR ID LANGLE
%left APP
%right DBLARROW
%left TIMES
%nonassoc DOT

%start <Ast.Raw.typ> typ_expr
%start <Ast.Raw.typ Ast.Raw.kind> kind_expr

%%

%inline binding:
| LPAR x=ID DBLCOLON k=kind RPAR
    { (x, k) }

undelimited_kind:
| PI b=binding k=kind { mkPi_binding b k }
| SIGMA b=binding k=kind { mkSigma_binding b k }

delimited_kind:
| STAR { RBase }
| k1=delimited_kind DBLARROW k2=delimited_kind { RArrow(k1, k2) }
| k1=delimited_kind TIMES k2=delimited_kind { RProd(k1, k2) }
| SINGLE LPAR t=typ RPAR { RSingle t }
| LPAR k=kind RPAR { k }

kind:
| k=undelimited_kind | k=delimited_kind
    { k }

kind_expr:
| k=kind EOF { k }

undelimited_typ:
| LAMBDA b=binding t=typ
    { mkLam_binding b t $startpos $endpos }

delimited_typ:
| LPAR t=typ RPAR { t }
| x=ID { locate (RVar x) $startpos $endpos }
| t1=delimited_typ t2=delimited_typ                 %prec APP
    { locate (RApp(t1, t2)) $startpos $endpos }
| LANGLE t1=delimited_typ COMMA t2=typ RANGLE
    { locate (RPair(t1, t2)) $startpos $endpos }
| t=delimited_typ DOT x=ID
    { locate (RProj(t, x)) $startpos $endpos }

typ:
| t=undelimited_typ | t=delimited_typ
    { t }

typ_expr:
| t=typ EOF { t }

%%

