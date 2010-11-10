(** Typing environments. *)

(** The type of environments.
    It is generic with respect to the types of the information associated
    to term variables and to type variables. *)
type ('a, 'b) t

(** The empty environment. *)
val empty: ('a, 'b) t

module Term: sig

  type var = Ast.Term.Var.free

(** [get_var x env] returns the info (usually a type) associated
    to [x] in [env].
    @raise Not_found if the variable is not present. *)
  val get_var: var -> ('a, 'b) t -> 'a

(** [add_var x t env] returns the environment [env] with the extra
    binding [(x, t)]. *)
  val add_var: var -> 'a -> ('a, 'b) t -> ('a, 'b) t

end

module Typ: sig

  type var = Ast.Typ.Var.free

(** [get_var x env] returns the info (usually a kind) associated
    to [x] in [env].
    @raise Not_found if the variable is not present. *)
  val get_var: var -> ('a, 'b) t -> 'b


(** [add_var x k env] returns the environment [env] with the extra
    binding [(x, k)]. *)
  val add_var: var -> 'b -> ('a, 'b) t -> ('a, 'b) t

end
