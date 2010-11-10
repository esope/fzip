open Location

module Raw = struct

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
(* base types *)
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

module Typ = struct
  module Var : Var.S = Var.Make(struct let fbase = "α" let bbase = "α__" end)

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

  type t = typ

  let h_max f m =
    Label.Map.fold (fun _lab x acc -> Var.bmax (f x) acc) m Var.bzero

  let rec h_sigmas h_kind (x: Var.free) = function
    | [] -> Var.bzero
    | (_label, (y, k)) :: l ->
        let n = Var.bmax (h_kind x k) (h_sigmas h_kind x l) in
        if Var.bequal n Var.bzero then n else Var.bmax n (Var.bsucc y)

  let rec h_kind_rec h_typ (x : Var.free) = function
    | Base -> Var.bzero
    | Sigma f -> h_sigmas (h_kind_rec h_typ) x f
    | Pi(y, k1, k2) ->
        let n = Var.bmax (h_kind_rec h_typ x k1) (h_kind_rec h_typ x k2) in
        if Var.bequal n Var.bzero then n else Var.bmax n (Var.bsucc y)
    | Single t -> h_typ x t

  let rec pre_h_typ_rec h_kind (x : Var.free) = function
    | FVar y -> if Var.equal x y then Var.bone else Var.bzero
    | BVar _ -> Var.bzero
    | App (t,u) | BaseArrow(t, u) ->
        Var.bmax (h_typ_rec h_kind x t) (h_typ_rec h_kind x u)
    | Lam (y, k, t) | BaseForall(y, k, t) ->
        let n = Var.bmax (h_kind x k.content) (h_typ_rec h_kind x t) in
        if Var.bequal n Var.bzero then n else Var.bmax n (Var.bsucc y)
    | Proj(t, _) -> h_typ_rec h_kind x t
    | BaseRecord m | Record m -> h_max (h_typ_rec h_kind x) m
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
    | Sigma f ->
        Sigma
          (Label.AList.map
             (fun (x, k) -> (x, var_map_kind_rec var_map_typ f_free k)) f)
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
    | Record m ->
        Record (Label.Map.map (var_map_typ_rec var_map_kind f_free) m)
    | Proj (t, lab) ->
        Proj(var_map_typ_rec var_map_kind f_free t, lab)
    | BaseForall (x, k, t) ->
        BaseForall (x,
                    {k with content = var_map_kind f_free k.content },
                    var_map_typ_rec var_map_kind f_free t)
    | BaseRecord m ->
        BaseRecord (Label.Map.map (var_map_typ_rec var_map_kind f_free) m)
    | BaseArrow (t1, t2) ->
        BaseArrow(var_map_typ_rec var_map_kind f_free t1,
                  var_map_typ_rec var_map_kind f_free t2)
  and var_map_typ_rec var_map_kind f_free t =
    { t with
      content = pre_var_map_typ_rec var_map_kind f_free t.content }

(* closing recursion *)
  let rec var_map_kind f_free k = var_map_kind_rec var_map_typ f_free k
  and var_map_typ f_free k = var_map_typ_rec var_map_kind f_free k

  let var_map = var_map_typ

  let subst t x u =
    var_map_typ
      (fun y -> if Var.equal x y then u else FVar y)
      t

  let rec bsubst_kind_fields bsubst_kind f x u = match f with
  | [] -> []
  | (label, (y, k)) :: f when Var.bequal x y ->
      (label, (y, bsubst_kind k x u)) :: f
  | (label, (y, k)) :: f ->
      (label, (y, bsubst_kind k x u)) :: (bsubst_kind_fields bsubst_kind f x u)

  let rec bsubst_kind_rec bsubst_typ k x u = match k with
  | Base as k -> k
  | Pi(y, k1, k2) ->
      let k1' = bsubst_kind_rec bsubst_typ k1 x u in
      if Var.bequal x y
      then Pi(y, k1', k2)
      else Pi(y, k1', bsubst_kind_rec bsubst_typ k2 x u)
  | Sigma f ->
      Sigma (bsubst_kind_fields (bsubst_kind_rec bsubst_typ) f x u)
  | Single t ->
      Single (bsubst_typ t x u)

  let rec pre_bsubst_typ_rec bsubst_kind t x u = match t with
  | (FVar _) as v -> v
  | (BVar y) as b -> if Var.bequal x y then u.content else b
  | App (t1, t2) ->
      App(bsubst_typ_rec bsubst_kind t1 x u,
          bsubst_typ_rec bsubst_kind t2 x u)
  | Lam (y, k, t) ->
      let k' = { k with content = bsubst_kind k.content x u } in
      if Var.bequal x y
      then Lam(y, k', t)
      else Lam (y, k', bsubst_typ_rec bsubst_kind t x u)
  | Record m ->
      Record (Label.Map.map (fun t -> bsubst_typ_rec bsubst_kind t x u) m)
  | Proj (t, lab) ->
      Proj(bsubst_typ_rec bsubst_kind t x u, lab)
  | BaseForall (y, k, t) ->
      let k' = { k with content = bsubst_kind k.content x u } in
      if Var.bequal x y
      then BaseForall (y, k', t)
      else BaseForall (y, k', bsubst_typ_rec bsubst_kind t x u)
  | BaseRecord m ->
      BaseRecord (Label.Map.map (fun t -> bsubst_typ_rec bsubst_kind t x u) m)
  | BaseArrow (t1, t2) ->
      BaseArrow (bsubst_typ_rec bsubst_kind t1 x u,
                 bsubst_typ_rec bsubst_kind t2 x u)
  and bsubst_typ_rec bsubst_kind t x u =
    { t with
      content = pre_bsubst_typ_rec bsubst_kind t.content x u }

(* closing recursion *)
  let rec bsubst_kind k x u = bsubst_kind_rec bsubst_typ k x u
  and bsubst_typ t x u = bsubst_typ_rec bsubst_kind t x u

  let bsubst = bsubst_typ

  let rec equal_kind_fields equal_kind f1 f2 = match(f1, f2) with
  | ([], []) -> true
  | ((lab1, (x1, k1)) :: f1, (lab2, (x2, k2)) :: f2) ->
      Label.equal lab1 lab2 && Var.bequal x1 x2 && equal_kind k1 k2
        && equal_kind_fields equal_kind f1 f2
  | (([] | _ :: _), _) -> false

  let rec equal_kind_rec equal_typ k1 k2 = match (k1, k2) with
  | (Base, Base) -> true
  | (Sigma f1, Sigma f2) ->
      equal_kind_fields (equal_kind_rec equal_typ) f1 f2
  | (Pi(x,k1,k2), Pi(x',k1',k2')) ->
      Var.bequal x x' && equal_kind_rec equal_typ k1 k1' && equal_kind_rec equal_typ k2 k2'
  | (Single t, Single t') ->
      equal_typ t t'
  | ((Base| Pi(_,_,_) | Sigma _ | Single _), _)-> false

  let rec equal_typ_rec equal_kind t1 t2 =
    pre_equal_typ_rec equal_kind t1.content t2.content
  and pre_equal_typ_rec equal_kind t1 t2 = match (t1, t2) with
  | (FVar x, FVar x') -> Var.equal x x'
  | (BVar x, BVar x') -> Var.bequal x x'
  | (Lam(x,k,t), Lam(x',k',t')) | (BaseForall(x,k,t), BaseForall(x',k',t')) ->
      Var.bequal x x' && equal_kind k.content k'.content && equal_typ_rec equal_kind t t'
  | (App(t1,t2), App(t1',t2')) | (BaseArrow(t1,t2), BaseArrow(t1',t2')) ->
      equal_typ_rec equal_kind t1 t1' && equal_typ_rec equal_kind t2 t2'
  | (BaseRecord m, BaseRecord m') | (Record m, Record m') ->
      Label.Map.equal (equal_typ_rec equal_kind) m m'
  | (Proj(t,lab), Proj(t',lab')) ->
      equal_typ_rec equal_kind t t' && Label.equal lab.content lab'.content
  | ((FVar _ | BVar _ | Lam(_,_,_) | Record _ | BaseRecord _ |
    BaseArrow(_,_) | BaseForall(_,_,_) | App(_,_) | Proj(_,_)), _) -> false

(* closing recursion *)
  let rec equal_kind k1 k2 = equal_kind_rec equal_typ k1 k2
  and equal_typ t1 t2 = equal_typ_rec equal_kind t1 t2

  let equal = equal_typ

(* smart constructors *)
  let mkLam x tau t =
    let y = h_typ x t in
    Lam (y, tau, subst t x (BVar y))

  let mkBaseForall x k t =
    let y = h_typ x t in
    BaseForall (y, k, subst t x (BVar y))
end

module Kind = struct
  type 'a kind = 'a Typ.kind =
    | Base
    | Pi of Typ.Var.bound * 'a kind * 'a kind
    | Sigma of (Typ.Var.bound * 'a kind) Label.AList.t
    | Single of 'a

  type t = Typ.t kind

  let var_map = Typ.var_map_kind

  let subst k x u =
    var_map
      (fun y -> if Typ.Var.equal x y then u else Typ.FVar y)
      k

  let subst_fields f x u =
    Label.AList.map (fun (y, k) -> (y, subst k x u)) f

  let bsubst = Typ.bsubst_kind

  let bsubst_fields f x u = Typ.bsubst_kind_fields bsubst f x u

  let equal = Typ.equal_kind

  let mkPi x k1 k2 =
    let y = Typ.h_kind x k2 in
    Pi (y, k1, subst k2 x (Typ.BVar y))

  let mkArrow k1 k2 = 
    let x = Typ.Var.fresh () in
    mkPi x k1 k2

  let mkSigma = 
    let rec aux : (Typ.Var.free * Typ.t kind) Label.AList.t
      -> (Typ.Var.bound * Typ.t kind) Label.AList.t = function
      | [] -> []
      | (lab, (x, k)) :: f ->
          let f = aux f in
          let y = Typ.h_sigmas Typ.h_kind x f in
          (lab, (y, k)) :: (subst_fields f x (Typ.BVar y))
    in fun f -> Sigma (aux f)

end


module Term = struct
  module Var : Var.S = Var.Make(struct let fbase = "x" let bbase = "x__" end)

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

  type t = term

  let h_term_max f m =
    Label.AList.fold (fun _lab x acc -> Var.bmax (f x) acc) m Var.bzero

  let h_typ_max f m =
    Label.AList.fold (fun _lab x acc -> Typ.Var.bmax (f x) acc) m Typ.Var.bzero

  let rec pre_h_term_var (x : Var.free) = function
    | FVar y -> if Var.equal x y then Var.bone else Var.bzero
    | BVar _ -> Var.bzero
    | App (t,u) -> Var.bmax (h_term_var x t) (h_term_var x u)
    | Lam (y, _tau, t) ->
        let n = h_term_var x t in
        if Var.bequal n Var.bzero then n else Var.bmax n (Var.bsucc y)
    | Proj(t, _) | Inst(t, _) | Gen (_, _, t) -> h_term_var x t
    | Record m -> h_term_max (h_term_var x) m
  and h_term_var (x : Var.free) t =
    pre_h_term_var x t.content

  let rec pre_h_typ_var (x : Typ.Var.free) = function
    | FVar _ | BVar _ -> Typ.Var.bzero
    | App (t,u) ->
        Typ.Var.bmax (h_typ_var x t) (h_typ_var x u)
    | Lam (_, tau, t) ->
        Typ.Var.bmax (Typ.h_typ x tau) (h_typ_var x t)
    | Gen (y, k, t) ->
        let n = Typ.Var.bmax (Typ.h_kind x k.content) (h_typ_var x t) in
        if Typ.Var.bequal n Typ.Var.bzero then n
        else Typ.Var.bmax n (Typ.Var.bsucc y)
    | Proj(t, _) | Inst(t, _) -> h_typ_var x t
    | Record m -> h_typ_max (h_typ_var x) m
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
    | Record m ->
        Record (Label.AList.map (var_map_term_var f_free) m)
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
      (fun y -> if Var.equal x y then u else FVar y)
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
    | Record m ->
        Record (Label.AList.map (var_map_typ_var f_free) m)
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
      (fun y -> if Typ.Var.equal x y then u else Typ.FVar y)
      t

  let rec pre_bsubst_term_var t x u = match t with
  | (FVar _) as v -> v
  | (BVar y) as b -> if Var.bequal x y then u.content else b
  | App (t1, t2) ->
      App(bsubst_term_var t1 x u,
          bsubst_term_var t2 x u)
  | Lam (y, k, t) ->
      if Var.bequal x y
      then Lam(y, k, t)
      else Lam (y, k, bsubst_term_var t x u)
  | Record m ->
      Record (Label.AList.map (fun t -> bsubst_term_var t x u) m)
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
  | Record m ->
      Record (Label.AList.map (fun t -> bsubst_typ_var t x u) m)
  | Proj (t, lab) ->
      Proj(bsubst_typ_var t x u, lab)
  | Gen(y, k, t) ->
      let k' = { k with content = Typ.bsubst_kind k.content x u } in
      if Typ.Var.bequal x y
      then Gen(y, k', t)
      else Gen (y, k', bsubst_typ_var t x u)
  | Inst(t, tau) ->
      Inst(bsubst_typ_var t x u,
           Typ.bsubst_typ tau x u)
  and bsubst_typ_var t x u =
    { t with
      content = pre_bsubst_typ_var t.content x u }

  let rec equal t1 t2 = pre_equal t1.content t2.content
  and pre_equal t1 t2 = match (t1, t2) with
  | (FVar x, FVar x') -> Var.equal x x'
  | (BVar x, BVar x') -> Var.bequal x x'
  | (Lam(x,tau,t), Lam(x',tau',t')) ->
      Var.bequal x x' && Typ.equal_typ tau tau' && equal t t'
  | (App(t1,t2), App(t1',t2')) ->
      equal t1 t1' && equal t2 t2'
  | (Record m, Record m') ->
      Label.AList.equal equal m m'
  | (Proj(t,lab), Proj(t',lab')) ->
      equal t t' && Label.equal lab.content lab'.content
  | (Gen(x,k,t), Gen(x',k',t')) ->
      Typ.Var.bequal x x' && Typ.equal_kind k.content k'.content && equal t t'
  | (Inst(t,tau), Inst(t',tau')) ->
      equal t t' && Typ.equal_typ tau tau'
  | ((FVar _ | BVar _ | Lam(_,_,_) | Record _ | Proj(_,_)
     | Gen(_,_,_) | App(_,_) | Inst(_,_)) ,_) -> false

(* smart constructors *)
  let mkLam x tau t =
    let y = h_term_var x t in
    Lam (y, tau, subst_term_var t x (BVar y))

  let mkGen x k t =
    let y = h_typ_var x t in
    Gen (y, k, subst_typ_var t x (Typ.BVar y))

end
