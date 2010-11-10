(** Abstract syntax trees. *)
open Location

(** raw syntax *)
module Raw : sig
  type 'a kind =
    | Base
    | Pi of string * 'a kind * 'a kind
    | Sigma of (string * 'a kind) Label.AList.t
    | Single of 'a * 'a kind

  type typ = pre_typ located
  and pre_typ =
    | Var of string
    | App of typ * typ
    | Lam of string * (typ kind) located * typ
    | Record of typ Label.Map.t
    | Proj of typ * Label.t located
(** base types *)
    | BaseForall of string * (typ kind) located * typ
    | BaseExists of string * (typ kind) located * typ
    | BaseRecord of typ Label.Map.t
    | BaseArrow of typ * typ

  type ('kind, 'typ) term = (('kind, 'typ) pre_term) located
  and ('kind, 'typ) pre_term =
    | TeVar of string
    | TeApp of ('kind, 'typ) term * ('kind, 'typ) term
    | TeLam of string * 'typ * ('kind, 'typ) term
    | TeRecord of (('kind, 'typ) term) Label.AList.t
    | TeProj of ('kind, 'typ) term * Label.t located
    | TeGen of string * 'kind located * ('kind, 'typ) term
    | TeInst of ('kind, 'typ) term * 'typ

end

(** AST for types *)
module Typ : sig
  module Var : Var.S

  type 'a kind = private
    | Base
    | Pi of Var.bound * 'a kind * 'a kind
    | Sigma of (Var.bound * 'a kind) Label.AList.t
    | Single of 'a * 'a kind

  type typ = pre_typ located
  and pre_typ = private
    | FVar of Var.free
    | BVar of Var.bound
    | App of typ * typ
    | Lam of Var.bound * (typ kind) located * typ
    | Record of typ Label.Map.t
    | Proj of typ * Label.t located
    | BaseForall of Var.bound * (typ kind) located * typ
    | BaseExists of Var.bound * (typ kind) located * typ
    | BaseRecord of typ Label.Map.t
    | BaseArrow of typ * typ

   type t = typ

(** map on free variables *)
  val var_map:  (Var.free -> pre_typ) -> t -> t

(** substitution of free variables *)
  val subst: t -> Var.free -> pre_typ -> t

(** substitution of bound variables *)
  val bsubst: t -> Var.bound -> t -> t

(** equality test *)
  val equal: t -> t -> bool

(** smart constructors *)
  val mkVar: Var.free -> pre_typ
  val mkApp: t -> t -> pre_typ
  val mkLam: Var.free -> t kind located -> t -> pre_typ
  val mkRecord: typ Label.Map.t -> pre_typ
  val mkProj: t -> Label.t located -> pre_typ
  val mkBaseForall: Var.free -> t kind located -> t -> pre_typ
  val mkBaseExists: Var.free -> t kind located -> t -> pre_typ
  val mkBaseRecord: typ Label.Map.t -> pre_typ
  val mkBaseArrow: t -> t -> pre_typ
end

module Kind : sig
  type 'a kind = 'a Typ.kind = private
    | Base
    | Pi of Typ.Var.bound * 'a kind * 'a kind
    | Sigma of (Typ.Var.bound * 'a kind) Label.AList.t
    | Single of 'a * 'a kind

  type t = Typ.t kind

(** map on free variables *)
  val var_map: (Typ.Var.free -> Typ.pre_typ) -> t -> t

(** substitution of free variables *)
  val subst: t -> Typ.Var.free -> Typ.pre_typ -> t
  val subst_fields:
      (Typ.Var.bound * t) Label.AList.t -> Typ.Var.free -> Typ.pre_typ
        -> (Typ.Var.bound * t) Label.AList.t

(** substitution of bound variables *)
  val bsubst: t -> Typ.Var.bound -> Typ.t -> t
  val bsubst_fields:
      (Typ.Var.bound * t) Label.AList.t -> Typ.Var.bound -> Typ.t
        -> (Typ.Var.bound * t) Label.AList.t

(** equality test *)
  val equal: t -> t -> bool

(** smart constructors *)
  val mkBase: t
  val mkSingle: Typ.t -> t -> t
  val mkPi: Typ.Var.free -> t -> t -> t
(** non-dependent version of mkPi *)
  val mkArrow: t -> t -> t
  val mkSigma: (Typ.Var.free * t) Label.AList.t -> t
end

(** AST for terms *)
module Term : sig
  module Var : Var.S

  type term = pre_term located
  and pre_term = private
    | FVar of Var.free
    | BVar of Var.bound
    | App of term * term
    | Lam of Var.bound * Typ.t * term
    | Record of term Label.AList.t
    | Proj of term * Label.t located
    | Gen of Typ.Var.bound * (Typ.typ Typ.kind) located * term
    | Inst of term * Typ.t

  type t = term

(** maps on free variables *)
  val var_map_term_var: (Var.free -> pre_term) -> t -> t
  val var_map_typ_var: (Typ.Var.free -> Typ.pre_typ) -> t -> t

(** substitution of free variables *)
  val subst_term_var: t -> Var.free -> pre_term -> t
  val subst_typ_var: t -> Typ.Var.free -> Typ.pre_typ -> t

(** substitution of bound variables *)
  val bsubst_term_var: t -> Var.bound -> t -> t
  val bsubst_typ_var: t -> Typ.Var.bound -> Typ.typ -> t

(** equality test *)
  val equal: t -> t -> bool

(** smart constructors *)
  val mkVar: Var.free -> pre_term
  val mkApp: t -> t -> pre_term
  val mkLam: Var.free -> Typ.typ -> t -> pre_term
  val mkRecord: t Label.AList.t -> pre_term
  val mkProj: t -> Label.t located -> pre_term
  val mkGen: Typ.Var.free -> Typ.typ Typ.kind located -> t -> pre_term
  val mkInst: t -> Typ.t -> pre_term

end

