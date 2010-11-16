(** Typing environments. *)

(** The type of environments.
    It is generic with respect to the types of the information associated
    to term variables and to type variables. *)
type t

(** The empty environment. *)
val empty: t

(** Purity test of an environment. *)
val is_pure: t -> Answer.t

(** Zipping of two contexts. *)
val zip: t -> t -> (t) Answer.WithValue.t

module Term: sig

  type var = Ast.Term.Var.free

(** [get_var x env] returns the info (usually a type) associated
    to [x] in [env].
    @raise Not_found if the variable is not present. *)
  val get_var: var -> t -> Ast.Typ.t

(** [add_var x t env] returns the environment [env] with the extra
    binding [(x, t)]. *)
  val add_var: var -> Ast.Typ.t -> t -> t

end

module Typ: sig

  type var = Ast.Typ.Var.free
  type mode = Mode.mode

(** [get_var x env] returns the info (usually a kind) associated
    to [x] in [env].
    @raise Not_found if the variable is not present. *)
  val get_var: var -> t -> mode Location.located * Ast.Kind.t


(** [add_var x k env] returns the environment [env] with the extra
    binding [(x, k)]. *)
  val add_var: mode Location.located -> var -> Ast.Kind.t -> t -> t

end
