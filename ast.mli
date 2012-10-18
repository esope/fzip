(** Abstract syntax trees. *)
open Location

(** raw syntax *)
module Raw : sig
  type 'a kind =
    | Base
    | Pi of string option * 'a kind * 'a kind
    | Sigma of (string option * 'a kind) Label.AList.t
    | Single of 'a * 'a kind

  type typ = pre_typ located
  and pre_typ =
    | Var of string
    | App of typ * typ
    | Lam of string located * (typ kind) located * typ
    | Record of typ Label.Map.t
    | Proj of typ * Label.t located
(** base types *)
    | BaseForall of string located * (typ kind) located * typ
    | BaseExists of string located * (typ kind) located * typ
    | BaseRecord of typ Label.Map.t
    | BaseArrow of typ * typ

  type ('kind, 'typ) term = (('kind, 'typ) pre_term) located
  and ('kind, 'typ) pre_term =
    | TeVar of string
    | TeApp of ('kind, 'typ) term * ('kind, 'typ) term
    | TeLam of string located * 'typ * ('kind, 'typ) term
    | TeLet of string located * ('kind, 'typ) term * ('kind, 'typ) term
    | TeRecord of ((string located) option * ('kind, 'typ) term) Label.AList.t
    | TeProj of ('kind, 'typ) term * Label.t located
    | TeGen of string located * 'kind located * ('kind, 'typ) term
    | TeInst of ('kind, 'typ) term * 'typ
    | TeAnnot of ('kind, 'typ) term * 'typ
    | TeEx of string located * 'kind located * ('kind, 'typ) term
    | TeNu of string located * 'kind located * ('kind, 'typ) term
    | TeOpen of string located * ('kind, 'typ) term
    | TeSigma of string located *
          string located * 'kind located * 'typ * ('kind, 'typ) term
    | TeFix of string located * 'typ * ('kind, 'typ) term

  type req =
    | RequireVal of string located * typ
    | RequireTyp of string located * (typ kind) located
    | ExportTyp of string located * (typ kind) located
  type reqs = req list

  type prog = { reqs : reqs ; code : (typ kind, typ) term }

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
    | Lam of Var.bound located * (typ kind) located * typ
    | Record of typ Label.Map.t
    | Proj of typ * Label.t located
    | BaseForall of Var.bound located * (typ kind) located * typ
    | BaseExists of Var.bound located * (typ kind) located * typ
    | BaseRecord of typ Label.Map.t
    | BaseArrow of typ * typ

   type t = typ

(** decides whether some bound variable occurs. *)
  val bvar_occurs: Var.bound -> t -> bool

(** map on free variables *)
  val var_map:  (Var.free -> pre_typ) -> t -> t

(** substitution of free variables *)
  val subst: t -> Var.free -> pre_typ -> t

(** substitution of bound variables *)
  val bsubst: t -> Var.bound -> t -> t

(** equality test *)
  val equal: t -> t -> bool

(** computes the set of free type variables *)
  val fv: t -> Var.Set.t

(** decides whether a type variable is free in a type *)
  val is_fv: Var.free -> t -> bool

(** smart constructors *)
  val mkVar: Var.free -> pre_typ
  val mkApp: t -> t -> pre_typ
  val mkLam: Var.free located -> t kind located -> t -> pre_typ
  val mkRecord: typ Label.Map.t -> pre_typ
  val mkProj: t -> Label.t located -> pre_typ
  val mkBaseForall: Var.free located -> t kind located -> t -> pre_typ
  val mkBaseExists: Var.free located -> t kind located -> t -> pre_typ
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

(** decides whether some bound variable occurs. *)
  val bvar_occurs: Typ.Var.bound -> t -> bool
  val bvar_occurs_fields:
      Typ.Var.bound -> (Typ.Var.bound * 'a kind) Label.AList.t -> bool

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

(** computes the set of free type variables *)
  val fv: t -> Typ.Var.Set.t

(** decides whether a type variable is free in a kind *)
  val is_fv: Typ.Var.free -> t -> bool

(** smart constructors *)
  val mkBase: t
  val mkSingle: Typ.t -> t -> t
  val mkPi: Typ.Var.free -> t -> t -> t
(** non-dependent version of mkPi *)
  val mkArrow: t -> t -> t
  val mkSigma: (Typ.Var.free * t) Label.AList.t -> t

end

(** AST for terms. *)
module Term : sig
  module Var : Var.S

  type term = pre_term located
  and pre_term = private
(** System F with records. *)
    | FVar of Var.free
    | BVar of Var.bound
    | App of term * term
    | Lam of Var.bound located * Typ.t * term
    | Let of Var.bound located * term * term
    | Record of (Var.bound located * term) Label.AList.t
    | Proj of term * Label.t located
    | Gen of Typ.Var.bound located * (Kind.t) located * term
    | Inst of term * Typ.t
(** Fixpoint. *)
    | Fix of Var.bound located * Typ.t * term
(** Constructs for open existential types. *)
    | Annot of term * Typ.t
    | Ex of Typ.Var.bound located * Kind.t located * term
    | Nu of Typ.Var.bound located * Kind.t located * term
    | Open of Typ.t * term (** the first argument is always a variable! *)
    | Sigma of
        Typ.t * Typ.Var.bound located * Kind.t located * Typ.t * term
          (** the first argument is always a variable! *)

  type t = term

(** decides whether some bound variable occurs. *)
  val term_bvar_occurs: Var.bound -> t -> bool
  val typ_bvar_occurs: Typ.Var.bound -> t -> bool

(** maps on free variables *)
  val var_map_term_var: (Var.free -> pre_term) -> t -> t
  val var_map_typ_var: (Typ.Var.free -> Typ.pre_typ) -> t -> t

(** substitution of free variables *)
  val subst_term_var: t -> Var.free -> pre_term -> t
  val subst_term_fields:
      (Var.bound * t) Label.AList.t -> Var.free -> pre_term
        -> (Var.bound * t) Label.AList.t
  val subst_typ_var: t -> Typ.Var.free -> Typ.pre_typ -> t
  val subst_typ_fields:
      (Var.bound * t) Label.AList.t -> Typ.Var.free -> Typ.pre_typ
        -> (Var.bound * t) Label.AList.t

(** substitution of bound variables *)
  val bsubst_term_var: t -> Var.bound -> t -> t
  val bsubst_term_fields:
      (Var.bound located * t) Label.AList.t -> Var.bound -> t
        -> (Var.bound located * t) Label.AList.t
  val bsubst_typ_var: t -> Typ.Var.bound -> Typ.typ -> t
  val bsubst_typ_fields:
      (Var.bound located * t) Label.AList.t -> Typ.Var.bound -> Typ.typ
        -> (Var.bound located * t) Label.AList.t

(** equality test *)
  val equal: t -> t -> bool

(** computes the set of free type variables *)
  val fv_typ: t -> Typ.Var.Set.t

(** decides whether a type variable is free in a term *)
  val is_fv_typ: Typ.Var.free -> t -> bool

(** computes the set of free term variables *)
  val fv_term: t -> Var.Set.t

(** decides whether a term variable is free in a term *)
  val is_fv_term: Var.free -> t -> bool

(** smart constructors *)
  val mkVar: Var.free -> pre_term
  val mkApp: t -> t -> pre_term
  val mkLam: Var.free located -> Typ.t -> t -> pre_term
  val mkLet: Var.free located -> t -> t -> pre_term
  val mkRecord: (Var.free located * t) Label.AList.t -> pre_term
  val mkProj: t -> Label.t located -> pre_term
  val mkGen: Typ.Var.free located -> Kind.t located -> t -> pre_term
  val mkInst: t -> Typ.t -> pre_term
  val mkFix: Var.free located -> Typ.t -> t -> pre_term
  val mkAnnot: t -> Typ.t -> pre_term
  val mkEx: Typ.Var.free located -> Kind.t located -> t -> pre_term
  val mkNu: Typ.Var.free located -> Kind.t located -> t -> pre_term
  val mkOpen: Typ.Var.free located -> t -> pre_term
  val mkSigma: Typ.Var.free located ->
    Typ.Var.free located -> Kind.t located -> Typ.t -> t -> pre_term

end

module Prog: sig
  type req =
    | RequireVal of Term.Var.free located * Typ.t
    | RequireTyp of Typ.Var.free located * Kind.t located
    | ExportTyp of Typ.Var.free located * Kind.t located
  type reqs = req list

  type t = { reqs : reqs ; code : Term.t }

end
