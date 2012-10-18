(** Typechecking of programs. *)

open Ast
type t = Prog.t
type reqs = Prog.reqs

(** Decides the wellformedness of requirements. When if succeeds, it
    returns a pure environment and the set of exported type
    variables, along with their locations. Otherwise, it raises Error.ERROR.e *)
val wfreqs: reqs -> Env.t * (Mode.mode Location.located) Typ.Var.Map.t

val wfprog: t -> Typ.t
