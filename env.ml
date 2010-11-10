type typ_var = Ast.Typ.Var.free
type term_var = Ast.Term.Var.free

type ('a, 'b) t =
    { term_vars: (term_var * 'a) list ;
      typ_vars: (typ_var * 'b) list }

let empty = { term_vars = [] ; typ_vars = [] }

module Term = struct

  type var = term_var

  let get_var x e = List.assoc x e.term_vars

  let add_var x t e =
    { e with term_vars = (x, t) :: e.term_vars }

end

module Typ = struct

  type var = typ_var

  let get_var x e = List.assoc x e.typ_vars

  let add_var x k e =
    { e with typ_vars = (x, k) :: e.typ_vars }

end
