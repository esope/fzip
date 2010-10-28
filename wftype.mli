(** Checking types. *)
open Ast.Typ

module Sub_result : sig
  type 'a t = Yes | No of ('a * 'a) list
  val ( &*& ): 'a t -> 'a t -> 'a t
  val from_bool: bool -> 'a t
  val to_bool: 'a t -> bool
end

type env = (typ, typ kind) Env.t

(** Decides subkinding. *)
val wfsubkind: env -> typ kind -> typ kind -> (typ kind) Sub_result.t
val wfsubkind_b: env -> typ kind -> typ kind -> bool

(** Decides kind wellformedness. *)
val wfkind: env -> typ kind -> bool

(** Computes the minimal kind. *)
val wftype: env -> typ -> typ kind

(** Decides subtyping. *)
val wfsubtype: env -> typ -> typ -> typ Sub_result.t
val wfsubtype_b: env -> typ -> typ -> bool
