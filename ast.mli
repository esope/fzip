(** Abstract syntax trees. *)
open Location

(** raw syntax *)
module Raw : sig
  type 'a kind =
    | Base
    | Pi of string * 'a kind * 'a kind
    | Sigma of (string * 'a kind) Label.AList.t
    | Single of 'a

  type typ = pre_typ located
  and pre_typ =
    | Var of string
    | App of typ * typ
    | Lam of string * (typ kind) located * typ
    | Record of typ Label.Map.t
    | Proj of typ * Label.t located
(** base types *)
    | BaseForall of string * (typ kind) located * typ
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

  type 'a kind =
    | Base
    | Pi of Var.bound * 'a kind * 'a kind
    | Sigma of (Var.bound * 'a kind) Label.AList.t
    | Single of 'a

  type typ = pre_typ located
  and pre_typ =
    | FVar of Var.free
    | BVar of Var.bound
    | App of typ * typ
    | Lam of Var.bound * (typ kind) located * typ
    | Record of typ Label.Map.t
    | Proj of typ * Label.t located
    | BaseForall of Var.bound * (typ kind) located * typ
    | BaseRecord of typ Label.Map.t
    | BaseArrow of typ * typ

(** map on free variables *)
  val var_map_kind: (Var.free -> pre_typ) -> typ kind -> typ kind
  val var_map_typ:  (Var.free -> pre_typ) -> typ -> typ

(** substitution of free variables *)
  val subst_typ: typ -> Var.free -> pre_typ -> typ
  val subst_kind: typ kind -> Var.free -> pre_typ -> typ kind
  val subst_kind_fields:
      (Var.bound * typ kind) Label.AList.t -> Var.free -> pre_typ
        -> (Var.bound * typ kind) Label.AList.t

(** substitution of bound variables *)
  val bsubst_typ: typ -> Var.bound -> typ -> typ
  val bsubst_kind: typ kind -> Var.bound -> typ -> typ kind
  val bsubst_kind_fields:
      (Var.bound * typ kind) Label.AList.t -> Var.bound -> typ
        -> (Var.bound * typ kind) Label.AList.t

(** equality test *)
  val eq_kind: typ kind -> typ kind -> bool
  val eq_typ: typ -> typ -> bool

(** smart constructors *)
  val mkLam: Var.free -> typ kind located -> typ -> pre_typ
  val mkPi: Var.free -> typ kind -> typ kind -> typ kind
(** non-dependent version of mkPi *)
  val mkArrow: typ kind -> typ kind -> typ kind
  val mkSigma: (Var.free * typ kind) Label.AList.t -> typ kind
  val mkBaseForall: Var.free -> typ kind located -> typ -> pre_typ
end

(** AST for terms *)
module Term : sig
  module Var : Var.S

  type term = pre_term located
  and pre_term =
    | FVar of Var.free
    | BVar of Var.bound
    | App of term * term
    | Lam of Var.bound * Typ.typ * term
    | Record of term Label.AList.t
    | Proj of term * Label.t located
    | Gen of Typ.Var.bound * (Typ.typ Typ.kind) located * term
    | Inst of term * Typ.typ

(** maps on free variables *)
  val var_map_term_var: (Var.free -> pre_term) -> term -> term
  val var_map_typ_var: (Typ.Var.free -> Typ.pre_typ) -> term -> term

(** substitution of free variables *)
  val subst_term_var: term -> Var.free -> pre_term -> term
  val subst_typ_var: term -> Typ.Var.free -> Typ.pre_typ -> term

(** substitution of bound variables *)
  val bsubst_term_var: term -> Var.bound -> term -> term
  val bsubst_typ_var: term -> Typ.Var.bound -> Typ.typ -> term

(** equality test *)
  val eq: term -> term -> bool

(** smart constructors *)
  val mkLam: Var.free -> Typ.typ -> term -> pre_term
  val mkGen: Typ.Var.free -> Typ.typ Typ.kind located -> term -> pre_term

end

