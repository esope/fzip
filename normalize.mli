(** Normalization and equivalence of types. *)

open Ast.Typ

type env = (typ, typ kind) Env.t

(** given a type [ty] of kind [Sigma f] and a projection label [l],
    [select_kind_field l ty f] computes the kind of [ty.l] *)
val select_kind_field: string Location.located -> typ ->
  (Var.bound * typ kind) Label.AList.t -> typ kind

(** given a type [ty] of kind [Sigma f],
    [select_all_fields ty f] computes the map
    [lab -> (ty.l, kind of ty.l) ] *)
val select_all_fields: typ ->
  (Var.bound * typ kind) Label.AList.t -> (typ * typ kind) Label.Map.t

(** head_norm e tau returns (tau', o) where tau' is the head
    normal form of tau in the environment e. If tau' is a path, then
    o = Some k where k is its natural kind. If tau' is not a path,
    then o = None. *)
val head_norm: env -> typ -> (typ * (typ kind) option)

(** computes the normal form of a type at a given kind *)
val typ_norm: env -> typ -> typ kind -> typ

(** decides equivalence of types and kinds *)
val equiv_typ: env -> typ -> typ -> typ kind -> Answer.t
val equiv_typ_b: env -> typ -> typ -> typ kind -> bool
val equiv_kind: env -> typ kind -> typ kind -> Answer.t
val equiv_kind_b: env -> typ kind -> typ kind -> bool

(** Decides subtyping. *)
val sub_kind: env -> typ kind -> typ kind -> Answer.t
val sub_kind_b: env -> typ kind -> typ kind -> bool

