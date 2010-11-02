type typ_var = Ast.Typ.Var.free
type term_var = Ast.Term.Var.free

type ('a, 'b) t =
    { term_vars: (term_var * 'a) list ;
      typ_vars: (typ_var * 'b) list }

let empty = { term_vars = [] ; typ_vars = [] }

let get_term_var x e = List.assoc x e.term_vars
let get_typ_var x e = List.assoc x e.typ_vars

let add_term_var x t e =
  { e with term_vars = (x, t) :: e.term_vars }
let add_typ_var x k e =
  { e with typ_vars = (x, k) :: e.typ_vars }

