(** Mode of type variables. *)

type mode =
    | U (** Universal variable. *)
    | E (** Existential variable. *)
    | EQ of Ast.Typ.t (** Variable with an equation. *)
