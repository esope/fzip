(** Normalization and equivalence of types. *)

open Ast

type env = (Typ.t, Kind.t) Env.t

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

(** head_norm e tau returns (tau', o) where tau' is the head
    normal form of tau in the environment e. If tau' is a path, then
    o = Some k where k is its natural kind. If tau' is not a path,
    then o = None. *)
val head_norm: env -> Typ.t -> (Typ.t * Kind.t option)

(** computes the normal form of a type at a given kind *)
val typ_norm: env -> Typ.t -> Kind.t -> Typ.t

(** decides equivalence of types and kinds *)
val equiv_typ: env -> Typ.t -> Typ.t -> Kind.t -> Answer.t
val equiv_typ_b: env -> Typ.t -> Typ.t -> Kind.t -> bool
val equiv_kind: env -> Kind.t -> Kind.t -> Answer.t
val equiv_kind_b: env -> Kind.t -> Kind.t -> bool

(** Decides subkinding. *)
val sub_kind: env -> Kind.t -> Kind.t -> Answer.t
val sub_kind_b: env -> Kind.t -> Kind.t -> bool

