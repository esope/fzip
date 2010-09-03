(** Normalization and equivalence of types. *)

open Ast.Typ

type env = (typ, typ kind) Env.t

(** decides equivalence of types *)
val equiv_typ: env -> typ -> typ -> typ kind -> bool

(** decides equivalence of types by comparing normal forms *)
val equiv_typ_simple: env -> typ -> typ -> typ kind -> bool

(** computes the normal form of a type at a given kind *)
val typ_norm: env -> typ -> typ kind -> typ

