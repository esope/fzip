(** Normalization and equivalence of types. *)

open Ast.Typ

type env = (typ, typ kind) Env.t

(** head_norm e tau returns (tau', o) where tau' is the head
    normal form of tau in the environment e. If tau' is a path, then
    o = Some k where k is its natural kind. If tau' is not a path,
    then o = None. *)
val head_norm: env -> typ -> (typ * (typ kind) option)

(** decides equivalence of types *)
val equiv_typ: env -> typ -> typ -> typ kind -> Answer.t
val equiv_typ_b: env -> typ -> typ -> typ kind -> bool

(** decides equivalence of types by comparing normal forms *)
val equiv_typ_simple: env -> typ -> typ -> typ kind -> Answer.t
val equiv_typ_simple_b: env -> typ -> typ -> typ kind -> bool

(** computes the normal form of a type at a given kind *)
val typ_norm: env -> typ -> typ kind -> typ

