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

(** Removes the recorded removals of type variables. *)
val clean_removed_vars: t -> t

(** Conversion to a readable string, for pretty printing purpose. *)
val to_string: t -> string

module Term: sig

  type var = Ast.Term.Var.free

(** [get_var x env] returns the info (usually a type) associated
    to [x] in [env].
    @raise Removed_var if the variable was removed
    @raise Not_found if the variable is not present at all. *)
  val get_var: var -> t -> Ast.Typ.t

(** Decides whether a variable is in the domain of an environment. *)
  val mem_var: var -> t -> bool

(** [add_var x t env] returns the environment [env] with the extra
    binding [(x, t)]. *)
  val add_var: var -> Ast.Typ.t -> t -> t

(** [remove_var x loc env] returns [env] from which the first binding of [x]
    has been removed, if any. Otherwise, it returns [env]. If [track] is
    set to [true], then the removal of the variable is recorded with 
    the location [loc]. *)
  val remove_var: track:bool -> var -> unit Location.located -> t -> t

end

module Typ: sig

  type var = Ast.Typ.Var.free
  type mode = Mode.mode

(** [get_var x env] returns the info (usually a kind) associated
    to [x] in [env].
    @raise Removed_var if the variable was removed
    @raise Not_found if the variable is not present at all. *)
  val get_var: var -> t -> mode Location.located * Ast.Kind.t

(** Decides whether a variable is in the domain of an environment. *)
  val mem_var: var -> t -> bool

(** [add_var x k env] returns the environment [env] with the extra
    binding [(x, k)]. *)
  val add_var: mode Location.located -> var -> Ast.Kind.t -> t -> t

(** [remove_var a loc env] returns [env] from which the first binding of [a]
    has been removed, if any. Otherwise, it returns [env]. If [track] is
    set to [true], then the removal of the variable is recorded with
    the location [loc].
    If [recursive] is set to true, then every binding that depends on [a]
    is also removed.
    TODO: remove the bindings that depend on [a] as well. *)
  val remove_var: track:bool -> recursive:bool -> var ->
    unit Location.located -> t -> t

(** decides whether a type variable occurs in an environment *)
  val is_fv: Ast.Typ.Var.free -> t -> bool

(** returns the set of existential type variables, associate with
    their locations. *)
  val exist_vars: t -> (Mode.mode Location.located) Ast.Typ.Var.Map.t
end
