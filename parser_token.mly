%{

open Ast.Raw
let locate = Location.locate

let mkPi_binding (x,k) k' = Pi(Some x, k.Location.content, k')

let mkArrow k k' = Pi(None, k, k')

let mkLam_binding (x,k) t = locate (Lam(x, k, t))
let mkForall_binding (x,k) t = locate (BaseForall(x, k, t))
let mkExists_binding (x,k) t = locate (BaseExists(x, k, t))

let mkTeLam_binding (x,tau) t = locate (TeLam(x, tau, t))
let mkTeGen_binding (x,k) t = locate (TeGen(x, k, t))

%}

%token EOF

%token STAR DBLARROW

%token UPLAMBDA LAMBDA LPAR RPAR DBLCOLON FORALL ARROW APP EXISTS LET IN
%token LANGLE RANGLE DOT
%token SINGLE
%token PI
%token COLON RBRACE LBRACE EQ RBRACKET LBRACKET
%token VAL TYPE AS
%token <string> ID

%nonassoc LPAR ID LANGLE LBRACE LBRACKET
%left APP
%right DBLARROW
%right ARROW
%nonassoc DOT


%%
