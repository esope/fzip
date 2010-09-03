(** Typing environments. *)

(** The type of environments.
    It is generic with respect to the types of the information associated
    to term variables and to type variables. *)
type ('a, 'b) t

(** The empty environment. *)
val empty: ('a, 'b) t

(** [get_term_var x env] returns the info (usually a type) associated
    to [x] in [env].
    @raise Not_found if the variable is not present. *)
val get_term_var: string -> ('a, 'b) t -> 'a

(** [get_typ_var x env] returns the info (usually a kind) associated
    to [x] in [env].
    @raise Not_found if the variable is not present. *)
val get_typ_var: string -> ('a, 'b) t -> 'b

(** [add_term_var x t env] returns the environment [env] with the extra
    binding [(x, t)]. *)
val add_term_var: string -> 'a -> ('a, 'b) t -> ('a, 'b) t

(** [add_typ_var x k env] returns the environment [env] with the extra
    binding [(x, k)]. *)
val add_typ_var: string -> 'b -> ('a, 'b) t -> ('a, 'b) t

