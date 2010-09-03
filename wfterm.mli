(** Typeckecking of terms. *)
open Ast

type env = (Typ.typ, Typ.typ Typ.kind) Env.t

val wfterm: env -> Term.term -> Typ.typ

