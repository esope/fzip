(** Normalization and equivalence of types. *)

open Ast

(** given a type [ty] of kind [Sigma f] and a projection label [l],
    [select_kind_field l ty f] computes the kind of [ty.l] *)
val select_kind_field: string Location.located -> Typ.t ->
  (Typ.Var.bound * Kind.t) Label.AList.t -> Kind.t

(** given a type [ty] of kind [Sigma f],
    [select_all_fields ty f] computes the map
    [lab -> (ty.l, kind of ty.l) ] *)
val select_all_fields: Typ.t ->
  (Typ.Var.bound * Kind.t) Label.AList.t -> (Typ.t * Kind.t) Label.Map.t

(** simplifies a kind: if [k] is equal to S(t,k') and k' is different
    from [Base], then it pushes the singleton inside.
    Otherwise, k is unchanged. *)
val simplify_kind: Kind.t -> Kind.t

(** decides whether a type is a path *)
val is_path: Typ.t -> bool

(** head_norm e tau returns (tau', o) where tau' is the head
    normal form of tau in the environment e. If tau' is a path, then
    o = Some k where k is its natural kind. If tau' is not a path,
    then o = None. *)
val head_norm: unfold_eq:bool -> Env.t -> Typ.t -> (Typ.t * Kind.t option)

(** computes the normal form of a type at a given kind *)
val typ_norm: unfold_eq:bool -> Env.t -> Typ.t -> Kind.t -> Typ.t

(** decides equivalence of types and kinds *)
val equiv_typ: unfold_eq:bool -> Env.t -> Typ.t -> Typ.t -> Kind.t -> Answer.t
val equiv_typ_b: unfold_eq:bool -> Env.t -> Typ.t -> Typ.t -> Kind.t -> bool
val equiv_kind: unfold_eq:bool -> Env.t -> Kind.t -> Kind.t -> Answer.t
val equiv_kind_b: unfold_eq:bool -> Env.t -> Kind.t -> Kind.t -> bool

(** Decides subkinding. *)
val sub_kind: unfold_eq:bool -> Env.t -> Kind.t -> Kind.t -> Answer.t
val sub_kind_b: unfold_eq:bool -> Env.t -> Kind.t -> Kind.t -> bool

