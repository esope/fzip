%{

open Ast.Raw
let locate = Location.locate
let relocate = Location.relocate
let dummy_locate = Location.dummy_locate

let mkPi_binding (_startpos,x,k) k' =
  Pi(Some x.Location.content, k.Location.content, k')

let rec mkPi_bindings bs t = match bs with
| [] -> t
| b :: bs -> mkPi_binding b (mkPi_bindings bs t)

let mkArrow k k' = Pi(None, k, k')

let mkLam_binding (_startpos,x,k) t = locate (Lam(x, k, t))

let rec mkLam_bindings bs t endpos = match bs with
| [] -> t
| (startpos, _, _) as b :: bs ->
    mkLam_binding b (mkLam_bindings bs t endpos) startpos endpos

let mkForall_binding (_startpos,x,k) t = locate (BaseForall(x, k, t))
let rec mkForall_bindings bs t endpos = match bs with
| [] -> t
| (startpos, _, _) as b :: bs ->
    mkForall_binding b (mkForall_bindings bs t endpos) startpos endpos

let mkExists_binding (_startpos,x,k) t = locate (BaseExists(x, k, t))
let rec mkExists_bindings bs t endpos = match bs with
| [] -> t
| (startpos, _, _) as b :: bs ->
    mkExists_binding b (mkExists_bindings bs t endpos) startpos endpos

let mkTeLam_binding (x,tau) t = locate (TeLam(x, tau, t))
let mkTeGen_binding (_startpos,x,k) t = locate (TeGen(x, k, t))
let rec mkTeGen_bindings bs t endpos = match bs with
| [] -> t
| (startpos, _, _) as b :: bs ->
    mkTeGen_binding b (mkTeGen_bindings bs t endpos) startpos endpos

type mixed_binding =
  | TeBind of Lexing.position * string Location.located * typ
  | TyBind of
      Lexing.position * string Location.located * (typ kind) Location.located

let rec mkTe_mixed_bindings b e endpos = match b with
| [] -> e
| TeBind(startpos, x, t) :: b ->
    mkTeLam_binding (x, t) (mkTe_mixed_bindings b e endpos) startpos endpos
| TyBind(startpos, a, k) :: b ->
    mkTeGen_binding (startpos, a, k)
      (mkTe_mixed_bindings b e endpos) startpos endpos

%}

%token EOF

%token REQUIREMENTS IMPORT EXPORT

%token STAR DBLARROW

%token LPAR RPAR DBLCOLON FORALL EXISTS COMMA ARROW
%token LET IN UPLAMBDA LAMBDA
%token SIGMA NU OPEN
%token LANGLE RANGLE DOT
%token SINGLE PI
%token COLON RBRACE LBRACE EQ RBRACKET LBRACKET
%token VAL TYPE AS
%token <string> ID


%%
