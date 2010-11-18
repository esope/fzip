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

(** Indicates from which point a variable was removed. *)
exception Removed_var of unit Location.located

module Term: sig

  type var = Ast.Term.Var.free

(** [get_var x env] returns the info (usually a type) associated
    to [x] in [env].
    @raise Removed_var if the variable was removed
    @raise Not_found if the variable is not present at all. *)
  val get_var: var -> t -> Ast.Typ.t

(** [add_var x t env] returns the environment [env] with the extra
    binding [(x, t)]. *)
  val add_var: var -> Ast.Typ.t -> t -> t

(** [remove_var x env] returns [env] from which the first binding of [x]
    has been removed, if any. Otherwise, it returns [env]. *)
  val remove_var: var -> t -> t

end

module Typ: sig

  type var = Ast.Typ.Var.free
  type mode = Mode.mode

(** [get_var x env] returns the info (usually a kind) associated
    to [x] in [env].
    @raise Removed_var if the variable was removed
    @raise Not_found if the variable is not present at all. *)
  val get_var: var -> t -> mode Location.located * Ast.Kind.t


(** [add_var x k env] returns the environment [env] with the extra
    binding [(x, k)]. *)
  val add_var: mode Location.located -> var -> Ast.Kind.t -> t -> t

(** [remove_var a env] returns [env] from which the first binding of [a]
    has been removed, if any. Otherwise, it returns [env].
    TODO: remove the bindings that depend on [a] as well. *)
  val remove_var: var -> t -> t

(** decides whether a type variable occurs in an environment *)
  val is_fv: Ast.Typ.Var.free -> t -> bool

(** returns the set of existential type variables, associate with
    their locations. *)
  val exist_vars: t -> (Mode.mode Location.located) Ast.Typ.Var.Map.t
end
