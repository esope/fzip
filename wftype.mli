open Ast.Typ

type env = (typ, typ kind) Env.t

(* decides subkinding *)
val wfsubkind: env -> typ kind -> typ kind -> bool

(* decides kind wellformedness *)
val wfkind: env -> typ kind -> bool

(* computes the minimal kind *)
val wftype: env -> typ -> typ kind
