%{

open Ast.Raw
let locate = Location.locate

let mkPi_binding (x,k) k' = Pi(x, k.Location.content, k')
let mkSigma_binding (x,k) k' = Sigma(x, k.Location.content, k')

let mkArrow k k' =
  let x = Ast.Typ.new_var () in Pi(x, k, k')
let mkProd k k' =
  let x = Ast.Typ.new_var () in Sigma(x, k, k')

let mkLam_binding (x,k) t = locate (Lam(x, k, t))
let mkForall_binding (x,k) t = locate (BaseForall(x, k, t))

let mkTeLam_binding (x,tau) t = locate (TeLam(x, tau, t))
let mkTeGen_binding (x,k) t = locate (TeGen(x, k, t))

%}

%token EOF

%token STAR DBLARROW

%token UPLAMBDA LAMBDA LPAR RPAR DBLCOLON FORALL ARROW APP
%token LANGLE RANGLE COMMA DOT TIMES
%token SINGLE
%token PI SIGMA
%token COLON SEMICOLON RBRACE LBRACE EQ RBRACKET LBRACKET
%token <string> ID

%nonassoc LPAR ID LANGLE LBRACE LBRACKET
%left APP
%right DBLARROW
%right ARROW
%left TIMES
%nonassoc DOT


%%
