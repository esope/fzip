open Location

type label = string located

(** raw syntax *)
module Raw : sig
  type 'a kind =
    | Base
    | Pi of string * 'a kind * 'a kind
    | Sigma of string * 'a kind * 'a kind
    | Single of 'a

  type typ = pre_typ located
  and pre_typ =
    | Var of string
    | App of typ * typ
    | Lam of string * (typ kind) located * typ
    | Pair of typ * typ
    | Proj of typ * label
(** base types *)
    | BaseForall of string * (typ kind) located * typ
    | BaseProd of typ * typ
    | BaseArrow of typ * typ

  type ('kind, 'typ) term = (('kind, 'typ) pre_term) located
  and ('kind, 'typ) pre_term =
    | TeVar of string
    | TeApp of ('kind, 'typ) term * ('kind, 'typ) term
    | TeLam of string * 'typ * ('kind, 'typ) term
    | TePair of ('kind, 'typ) term * ('kind, 'typ) term
    | TeProj of ('kind, 'typ) term * label
    | TeGen of string * 'kind located * ('kind, 'typ) term
    | TeInst of ('kind, 'typ) term * 'typ

end

(** AST for types *)
module Typ : sig
  module Var : Var.S

  type 'a kind =
    | Base
    | Pi of Var.bound * 'a kind * 'a kind
    | Sigma of Var.bound * 'a kind * 'a kind
    | Single of 'a

  type typ = pre_typ located
  and pre_typ =
    | FVar of Var.free
    | BVar of Var.bound
    | App of typ * typ
    | Lam of Var.bound * (typ kind) located * typ
    | Pair of typ * typ
    | Proj of typ * label
    | BaseForall of Var.bound * (typ kind) located * typ
    | BaseProd of typ * typ
    | BaseArrow of typ * typ

(** map on free variables *)
  val var_map_kind: (Var.free -> pre_typ) -> typ kind -> typ kind
  val var_map_typ:  (Var.free -> pre_typ) -> typ -> typ

(** substitution of free variables *)
  val subst_typ: typ -> Var.free -> pre_typ -> typ
  val subst_kind: typ kind -> Var.free -> pre_typ -> typ kind

(** substitution of bound variables *)
  val bsubst_kind: typ kind -> Var.bound -> typ -> typ kind
  val bsubst_typ: typ -> Var.bound -> typ -> typ

(** equality test *)
  val eq_kind: typ kind -> typ kind -> bool
  val eq_typ: typ -> typ -> bool

(** smart constructors *)
  val mkLam: Var.free -> typ kind located -> typ -> pre_typ
  val mkPi: Var.free -> typ kind -> typ kind -> typ kind
(** non-dependent version of mkPi *)
  val mkArrow: typ kind -> typ kind -> typ kind
  val mkSigma: Var.free -> typ kind -> typ kind -> typ kind
 (** non-dependent version of mkSigma *)
  val mkProd: typ kind -> typ kind -> typ kind
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
    | Pair of term * term
    | Proj of term * label
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

