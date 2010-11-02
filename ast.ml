open Location

type label = string located

module Raw = struct

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
(* base types *)
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

module Typ = struct
  module Var : Var.S = Var.Make(struct let fbase = "α" let bbase = "α__" end)

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

  let rec h_kind_rec h_typ (x : Var.free) = function
    | Base -> Var.bzero
    | Pi(y, k1, k2) | Sigma(y, k1, k2) ->
        let n = Var.bmax (h_kind_rec h_typ x k1) (h_kind_rec h_typ x k2) in
        if n = Var.bzero then n else Var.bmax n (Var.bsucc y)
    | Single t -> h_typ x t

  let rec pre_h_typ_rec h_kind (x : Var.free) = function
    | FVar y -> if Var.equal x y then Var.bone else Var.bzero
    | BVar _ -> Var.bzero
    | App (t,u) | Pair(t, u) | BaseProd(t, u) | BaseArrow(t, u) ->
        Var.bmax (h_typ_rec h_kind x t) (h_typ_rec h_kind x u)
    | Lam (y, k, t) | BaseForall(y, k, t) ->
        let n = Var.bmax (h_kind x k.content) (h_typ_rec h_kind x t) in
        if Var.bequal n Var.bzero then n else Var.bmax n (Var.bsucc y)
    | Proj(t, _) -> h_typ_rec h_kind x t
  and h_typ_rec h_kind (x : Var.free) t =
    pre_h_typ_rec h_kind x t.content

(* closing recursion *)
  let rec h_kind x k = h_kind_rec h_typ x k
  and h_typ x t = h_typ_rec h_kind x t

  let rec var_map_kind_rec var_map_typ f_free = function
    | Base as k -> k
    | Pi(x, k1, k2) ->
        Pi(x, var_map_kind_rec var_map_typ f_free k1,
           var_map_kind_rec var_map_typ f_free k2)
    | Sigma(x, k1, k2) ->
        Sigma(x, var_map_kind_rec var_map_typ f_free k1,
              var_map_kind_rec var_map_typ f_free k2)
    | Single t ->
        Single (var_map_typ f_free t)

  let rec pre_var_map_typ_rec var_map_kind f_free = function
    | FVar x -> f_free x
    | (BVar _) as b -> b
    | App (t1, t2) ->
        App(var_map_typ_rec var_map_kind f_free t1,
            var_map_typ_rec var_map_kind f_free t2)
    | Lam (x, k, t) ->
        Lam (x,
             { k with content = var_map_kind f_free k.content },
             var_map_typ_rec var_map_kind f_free t)
    | Pair (t1, t2) ->
        Pair(var_map_typ_rec var_map_kind f_free t1,
             var_map_typ_rec var_map_kind f_free t2)
    | Proj (t, lab) ->
        Proj(var_map_typ_rec var_map_kind f_free t, lab)
    | BaseForall (x, k, t) ->
        BaseForall (x,
                    {k with content = var_map_kind f_free k.content },
                    var_map_typ_rec var_map_kind f_free t)
    | BaseProd (t1, t2) ->
        BaseProd(var_map_typ_rec var_map_kind f_free t1,
                 var_map_typ_rec var_map_kind f_free t2)
    | BaseArrow (t1, t2) ->
        BaseArrow(var_map_typ_rec var_map_kind f_free t1,
                  var_map_typ_rec var_map_kind f_free t2)
  and var_map_typ_rec var_map_kind f_free t =
    { t with
      content = pre_var_map_typ_rec var_map_kind f_free t.content }

(* closing recursion *)
  let rec var_map_kind f_free k = var_map_kind_rec var_map_typ f_free k
  and var_map_typ f_free k = var_map_typ_rec var_map_kind f_free k

  let subst_typ t x u =
    var_map_typ
      (fun y -> if x = y then u else FVar y)
      t

  let subst_kind k x u =
    var_map_kind
      (fun y -> if x = y then u else FVar y)
      k

  let rec bsubst_kind_rec bsubst_typ k x u = match k with
  | Base as k -> k
  | Pi(y, k1, k2) ->
      let k1' = bsubst_kind_rec bsubst_typ k1 x u in
      if x = y
      then Pi(y, k1', k2)
      else Pi(y, k1', bsubst_kind_rec bsubst_typ k2 x u)
  | Sigma(y, k1, k2) ->
      let k1' = bsubst_kind_rec bsubst_typ k1 x u in
      if x = y
      then Sigma(y, k1', k2)
      else Sigma(y, k1', bsubst_kind_rec bsubst_typ k2 x u)
  | Single t ->
      Single (bsubst_typ t x u)

  let rec pre_bsubst_typ_rec bsubst_kind t x u = match t with
  | (FVar _) as v -> v
  | (BVar y) as b -> if x = y then u.content else b
  | App (t1, t2) ->
      App(bsubst_typ_rec bsubst_kind t1 x u,
          bsubst_typ_rec bsubst_kind t2 x u)
  | Lam (y, k, t) ->
      let k' = { k with content = bsubst_kind k.content x u } in
      if x = y
      then Lam(y, k', t)
      else Lam (y, k', bsubst_typ_rec bsubst_kind t x u)
  | Pair (t1, t2) ->
      Pair(bsubst_typ_rec bsubst_kind t1 x u,
           bsubst_typ_rec bsubst_kind t2 x u)
  | Proj (t, lab) ->
      Proj(bsubst_typ_rec bsubst_kind t x u, lab)
  | BaseForall (y, k, t) ->
      let k' = { k with content = bsubst_kind k.content x u } in
      if x = y
      then BaseForall (y, k', t)
      else BaseForall (y, k', bsubst_typ_rec bsubst_kind t x u)
  | BaseProd (t1, t2) ->
      BaseProd (bsubst_typ_rec bsubst_kind t1 x u,
                bsubst_typ_rec bsubst_kind t2 x u)
  | BaseArrow (t1, t2) ->
      BaseArrow (bsubst_typ_rec bsubst_kind t1 x u,
                 bsubst_typ_rec bsubst_kind t2 x u)
  and bsubst_typ_rec bsubst_kind t x u =
    { t with
      content = pre_bsubst_typ_rec bsubst_kind t.content x u }

(* closing recursion *)
  let rec bsubst_kind k x u = bsubst_kind_rec bsubst_typ k x u
  and bsubst_typ t x u = bsubst_typ_rec bsubst_kind t x u

  let rec eq_kind_rec eq_typ k1 k2 = match (k1, k2) with
  | (Base, Base) -> true
  | (Pi(x,k1,k2), Pi(x',k1',k2')) | (Sigma(x,k1,k2), Sigma(x',k1',k2')) ->
      x = x' && eq_kind_rec eq_typ k1 k1' && eq_kind_rec eq_typ k2 k2'
  | (Single t, Single t') ->
      eq_typ t t'
  | _ -> false

  let rec eq_typ_rec eq_kind t1 t2 =
    pre_eq_typ_rec eq_kind t1.content t2.content
  and pre_eq_typ_rec eq_kind t1 t2 = match (t1, t2) with
  | (FVar x, FVar x') -> x = x'
  | (BVar x, BVar x') -> x = x'
  | (Lam(x,k,t), Lam(x',k',t')) | (BaseForall(x,k,t), BaseForall(x',k',t')) ->
      x = x' && eq_kind k.content k'.content && eq_typ_rec eq_kind t t'
  | (Pair(t1,t2), Pair(t1',t2')) | (App(t1,t2), App(t1',t2'))
  | (BaseProd(t1,t2), BaseProd(t1',t2'))
  | (BaseArrow(t1,t2), BaseArrow(t1',t2')) ->
      eq_typ_rec eq_kind t1 t1' && eq_typ_rec eq_kind t2 t2'
  | (Proj(t,lab), Proj(t',lab')) ->
      eq_typ_rec eq_kind t t' && lab.content = lab'.content
  | _ -> false

(* closing recursion *)
  let rec eq_kind k1 k2 = eq_kind_rec eq_typ k1 k2
  and eq_typ t1 t2 = eq_typ_rec eq_kind t1 t2

(* smart constructors *)
  let mkLam x tau t =
    let y = h_typ x t in
    Lam (y, tau, subst_typ t x (BVar y))

  let mkPi x k1 k2 =
    let y = h_kind x k2 in
    Pi (y, k1, subst_kind k2 x (BVar y))

  let mkArrow k1 k2 = 
    let x = Var.fresh () in
    mkPi x k1 k2

  let mkSigma x k1 k2 =
    let y = h_kind x k2 in
    Sigma (y, k1, subst_kind k2 x (BVar y))

  let mkProd k1 k2 = 
    let x = Var.fresh () in
    mkSigma x k1 k2

  let mkBaseForall x k t =
    let y = h_typ x t in
    BaseForall (y, k, subst_typ t x (BVar y))
end

module Term = struct
  module Var : Var.S = Var.Make(struct let fbase = "x" let bbase = "x__" end)

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

  let rec pre_h_term_var (x : Var.free) = function
    | FVar y -> if Var.equal x y then Var.bone else Var.bzero
    | BVar _ -> Var.bzero
    | App (t,u) | Pair(t, u) ->
        Var.bmax (h_term_var x t) (h_term_var x u)
    | Lam (y, tau, t) ->
        let n = h_term_var x t in
        if Var.bequal n Var.bzero then n else Var.bmax n (Var.bsucc y)
    | Proj(t, _) | Inst(t, _) | Gen (_, _, t) -> h_term_var x t
  and h_term_var (x : Var.free) t =
    pre_h_term_var x t.content

  let rec pre_h_typ_var (x : Typ.Var.free) = function
    | FVar _ | BVar _ -> Typ.Var.bzero
    | App (t,u) | Pair(t, u) ->
        Typ.Var.bmax (h_typ_var x t) (h_typ_var x u)
    | Lam (_, tau, t) ->
        Typ.Var.bmax (Typ.h_typ x tau) (h_typ_var x t)
    | Gen (y, k, t) ->
        let n = Typ.Var.bmax (Typ.h_kind x k.content) (h_typ_var x t) in
        if Typ.Var.bequal n Typ.Var.bzero then n
        else Typ.Var.bmax n (Typ.Var.bsucc y)
    | Proj(t, _) | Inst(t, _) -> h_typ_var x t
  and h_typ_var (x : Typ.Var.free) t =
    pre_h_typ_var x t.content

  let rec pre_var_map_term_var f_free = function
    | FVar x -> f_free x
    | (BVar _) as b -> b
    | App (t1, t2) ->
        App(var_map_term_var f_free t1,
            var_map_term_var f_free t2)
    | Lam (x, k, t) ->
        Lam (x,
             k,
             var_map_term_var f_free t)
    | Pair (t1, t2) ->
        Pair(var_map_term_var f_free t1,
             var_map_term_var f_free t2)
    | Proj (t, lab) ->
        Proj(var_map_term_var f_free t, lab)
    | Gen (x, k, t) ->
        Gen (x, k, var_map_term_var f_free t)
    | Inst(t, tau) ->
        Inst (var_map_term_var f_free t, tau)
  and var_map_term_var f_free t =
    { t with
      content = pre_var_map_term_var f_free t.content }

  let subst_term_var t x u =
    var_map_term_var
      (fun y -> if x = y then u else FVar y)
      t

  let rec pre_var_map_typ_var f_free = function
    | FVar _ | BVar _ as t -> t
    | App (t1, t2) ->
        App(var_map_typ_var f_free t1,
            var_map_typ_var f_free t2)
    | Lam (x, k, t) ->
        Lam (x,
             Typ.var_map_typ f_free k,
             var_map_typ_var f_free t)
    | Pair (t1, t2) ->
        Pair(var_map_typ_var f_free t1,
             var_map_typ_var f_free t2)
    | Proj (t, lab) ->
        Proj(var_map_typ_var f_free t, lab)
    | Gen (x, k, t) ->
        Gen (x,
             {k with content = Typ.var_map_kind f_free k.content },
             var_map_typ_var f_free t)
    | Inst(t, tau) ->
        Inst (var_map_typ_var f_free t,
              Typ.var_map_typ f_free tau)
  and var_map_typ_var f_free t =
    { t with
      content = pre_var_map_typ_var f_free t.content }

  let subst_typ_var t x u =
    var_map_typ_var
      (fun y -> if x = y then u else Typ.FVar y)
      t

  let rec pre_bsubst_term_var t x u = match t with
  | (FVar _) as v -> v
  | (BVar y) as b -> if x = y then u.content else b
  | App (t1, t2) ->
      App(bsubst_term_var t1 x u,
          bsubst_term_var t2 x u)
  | Lam (y, k, t) ->
      if x = y
      then Lam(y, k, t)
      else Lam (y, k, bsubst_term_var t x u)
  | Pair (t1, t2) ->
      Pair(bsubst_term_var t1 x u,
           bsubst_term_var t2 x u)
  | Proj (t, lab) ->
      Proj(bsubst_term_var t x u, lab)
  | Gen (y, k, t) ->
      Gen (y, k, bsubst_term_var t x u)
  | Inst (t, tau) ->
      Inst (bsubst_term_var t x u, tau)
  and bsubst_term_var t x u =
    { t with
      content = pre_bsubst_term_var t.content x u }

  let rec pre_bsubst_typ_var t x u = match t with
  | FVar _ | BVar _ -> t
  | App (t1, t2) ->
      App(bsubst_typ_var t1 x u,
          bsubst_typ_var t2 x u)
  | Lam (y, tau, t) ->
      Lam (y,
          Typ.bsubst_typ tau x u,
          bsubst_typ_var t x u)
  | Pair (t1, t2) ->
      Pair(bsubst_typ_var t1 x u,
           bsubst_typ_var t2 x u)
  | Proj (t, lab) ->
      Proj(bsubst_typ_var t x u, lab)
  | Gen(y, k, t) ->
      let k' = { k with content = Typ.bsubst_kind k.content x u } in
      if x = y
      then Gen(y, k', t)
      else Gen (y, k', bsubst_typ_var t x u)
  | Inst(t, tau) ->
      Inst(bsubst_typ_var t x u,
           Typ.bsubst_typ tau x u)
  and bsubst_typ_var t x u =
    { t with
      content = pre_bsubst_typ_var t.content x u }

  let rec eq t1 t2 = pre_eq t1.content t2.content
  and pre_eq t1 t2 = match (t1, t2) with
  | (FVar x, FVar x') -> x = x'
  | (BVar x, BVar x') -> x = x'
  | (Lam(x,tau,t), Lam(x',tau',t')) ->
      x = x' && Typ.eq_typ tau tau' && eq t t'
  | (Pair(t1,t2), Pair(t1',t2')) | (App(t1,t2), App(t1',t2')) ->
      eq t1 t1' && eq t2 t2'
  | (Proj(t,lab), Proj(t',lab')) ->
      eq t t' && lab.content = lab'.content
  | (Gen(x,k,t), Gen(x',k',t')) ->
      x = x' && Typ.eq_kind k.content k'.content && eq t t'
  | (Inst(t,tau), Inst(t',tau')) ->
      eq t t' && Typ.eq_typ tau tau'
  | _ -> false

(* smart constructors *)
  let mkLam x tau t =
    let y = h_term_var x t in
    Lam (y, tau, subst_term_var t x (BVar y))

  let mkGen x k t =
    let y = h_typ_var x t in
    Gen (y, k, subst_typ_var t x (Typ.BVar y))

end
