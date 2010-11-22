open Location

module Raw = struct

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
(* base types *)
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
    | TeRecord of (('kind, 'typ) term) Label.AList.t
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

module Typ = struct
  module Var : Var.S = Var.Make(struct let fbase = "α" let bbase = "α__" end)

  type 'a kind =
    | Base
    | Pi of Var.bound * 'a kind * 'a kind
    | Sigma of (Var.bound * 'a kind) Label.AList.t
    | Single of 'a * 'a kind

  type typ = pre_typ located
  and pre_typ =
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

  let bvar_occurs x _t = not (Var.bequal x Var.bzero)
      (* from Sato-Pollack, x is free iff it is not 0 *)

  let h_binder y h =
    if Var.bequal h Var.bzero then h else Var.bmax h (Var.bsucc y)

  (* computes the maximum of all the elements of the range of a map *)
  let h_max f m =
    Label.Map.fold (fun _lab x acc -> Var.bmax (f x) acc) m Var.bzero

  (* computes the height of a variable in a list of kind fields *)
  let rec h_sigmas h_kind (x: Var.free) = function
    | [] -> Var.bzero
    | (_label, (y, k)) :: l ->
        Var.bmax (h_kind x k) (h_binder y (h_sigmas h_kind x l))

  let rec h_kind_rec h_typ (x : Var.free) = function
    | Base -> Var.bzero
    | Sigma f -> h_sigmas (h_kind_rec h_typ) x f
    | Pi(y, k1, k2) ->
        Var.bmax (h_kind_rec h_typ x k1) (h_binder y (h_kind_rec h_typ x k2))
    | Single (t, k) ->
        Var.bmax (h_typ x t) (h_kind_rec h_typ x k)

  let rec pre_h_typ_rec h_kind (x : Var.free) = function
    | FVar y -> if Var.equal x y then Var.bone else Var.bzero
    | BVar _ -> Var.bzero
    | App (t,u) | BaseArrow(t, u) ->
        Var.bmax (h_typ_rec h_kind x t) (h_typ_rec h_kind x u)
    | Lam (y, k, t) | BaseForall(y, k, t) | BaseExists(y, k, t) ->
        Var.bmax (h_kind x k.content)
          (h_binder y.content (h_typ_rec h_kind x t))
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
    | Single (t, k) ->
        Single (var_map_typ f_free t, var_map_kind_rec var_map_typ f_free k)

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
    | BaseExists (x, k, t) ->
        BaseExists (x,
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
  | Single (t, k) ->
      Single (bsubst_typ t x u, bsubst_kind_rec bsubst_typ k x u)

  let rec pre_bsubst_typ_rec bsubst_kind t x u = match t with
  | (FVar _) as v -> v
  | (BVar y) as b -> if Var.bequal x y then u.content else b
  | App (t1, t2) ->
      App(bsubst_typ_rec bsubst_kind t1 x u,
          bsubst_typ_rec bsubst_kind t2 x u)
  | Lam (y, k, t) ->
      let k' = { k with content = bsubst_kind k.content x u } in
      if Var.bequal x y.content
      then Lam(y, k', t)
      else Lam (y, k', bsubst_typ_rec bsubst_kind t x u)
  | Record m ->
      Record (Label.Map.map (fun t -> bsubst_typ_rec bsubst_kind t x u) m)
  | Proj (t, lab) ->
      Proj(bsubst_typ_rec bsubst_kind t x u, lab)
  | BaseForall (y, k, t) ->
      let k' = { k with content = bsubst_kind k.content x u } in
      if Var.bequal x y.content
      then BaseForall (y, k', t)
      else BaseForall (y, k', bsubst_typ_rec bsubst_kind t x u)
  | BaseExists (y, k, t) ->
      let k' = { k with content = bsubst_kind k.content x u } in
      if Var.bequal x y.content
      then BaseExists (y, k', t)
      else BaseExists (y, k', bsubst_typ_rec bsubst_kind t x u)
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

  let bsubst t x u =
    if bvar_occurs x t
    then bsubst_typ t x u
    else t

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
  | (Single (t, k), Single (t', k')) ->
      equal_typ t t' && equal_kind_rec equal_typ k k'
  | ((Base| Pi(_,_,_) | Sigma _ | Single (_,_)), _)-> false

  let rec equal_typ_rec equal_kind t1 t2 =
    pre_equal_typ_rec equal_kind t1.content t2.content
  and pre_equal_typ_rec equal_kind t1 t2 = match (t1, t2) with
  | (FVar x, FVar x') -> Var.equal x x'
  | (BVar x, BVar x') -> Var.bequal x x'
  | (Lam(x,k,t), Lam(x',k',t')) | (BaseForall(x,k,t), BaseForall(x',k',t'))
  | (BaseExists(x,k,t), BaseExists(x',k',t')) ->
      Var.bequal x.content x'.content &&
      equal_kind k.content k'.content && equal_typ_rec equal_kind t t'
  | (App(t1,t2), App(t1',t2')) | (BaseArrow(t1,t2), BaseArrow(t1',t2')) ->
      equal_typ_rec equal_kind t1 t1' && equal_typ_rec equal_kind t2 t2'
  | (BaseRecord m, BaseRecord m') | (Record m, Record m') ->
      Label.Map.equal (equal_typ_rec equal_kind) m m'
  | (Proj(t,lab), Proj(t',lab')) ->
      equal_typ_rec equal_kind t t' && Label.equal lab.content lab'.content
  | ((FVar _ | BVar _ | Lam(_,_,_) | Record _ | BaseRecord _ |
    BaseArrow(_,_) | BaseForall(_,_,_) | BaseExists (_,_,_) | App(_,_) |
    Proj(_,_)), _) -> false

(* closing recursion *)
  let rec equal_kind k1 k2 = equal_kind_rec equal_typ k1 k2
  and equal_typ t1 t2 = equal_typ_rec equal_kind t1 t2

  let equal = equal_typ

(* free variables *)
let rec fv_kind_rec fv_typ = let open Var.Set in
function
  | Base -> empty
  | Single(t, k) ->
      union (fv_typ t) (fv_kind_rec fv_typ k)
  | Pi(_x, k1, k2) ->
      union (fv_kind_rec fv_typ k1) (fv_kind_rec fv_typ k2)
  | Sigma f ->
      Label.AList.fold
        (fun _lab (_x, k) acc -> union (fv_kind_rec fv_typ k) acc)
        f empty

let rec fv_typ_rec fv_kind t = pre_fv_typ_rec fv_kind t.content
and pre_fv_typ_rec fv_kind = let open Var.Set in
function
  | BVar _ -> empty
  | FVar x -> singleton x
  | Lam(_x, k, t) | BaseForall(_x, k, t) | BaseExists(_x, k, t) ->
      union (fv_kind k.content) (fv_typ_rec fv_kind t)
  | App(t1, t2) | BaseArrow(t1, t2) ->
      union (fv_typ_rec fv_kind t1) (fv_typ_rec fv_kind t2)
  | Proj(t, _lab) -> fv_typ_rec fv_kind t
  | Record m | BaseRecord m ->
      Label.Map.fold 
        (fun _lab t acc -> union (fv_typ_rec fv_kind t) acc)
        m empty

(* closing recursion *)
let rec fv_typ t = fv_typ_rec fv_kind t
and fv_kind k = fv_kind_rec fv_typ k

let fv = fv_typ

(* occurrence of a free type variable *)
let rec is_fv_kind_rec is_fv_typ y = function
  | Base -> false
  | Single(t, k) ->
      (is_fv_typ y t) || (is_fv_kind_rec is_fv_typ y k)
  | Pi(_x, k1, k2) ->
      (is_fv_kind_rec is_fv_typ y k1) || (is_fv_kind_rec is_fv_typ y k2)
  | Sigma f ->
      Label.AList.exists
        (fun _lab (_x, k) -> is_fv_kind_rec is_fv_typ y k)
        f

let rec is_fv_typ_rec is_fv_kind y t = pre_is_fv_typ_rec is_fv_kind y t.content
and pre_is_fv_typ_rec is_fv_kind y = function
  | BVar _ -> false
  | FVar x -> Var.equal x y
  | Lam(_x, k, t) | BaseForall(_x, k, t) | BaseExists(_x, k, t) ->
      (is_fv_kind y k.content) || (is_fv_typ_rec is_fv_kind y t)
  | App(t1, t2) | BaseArrow(t1, t2) ->
      (is_fv_typ_rec is_fv_kind y t1) || (is_fv_typ_rec is_fv_kind y t2)
  | Proj(t, _lab) -> is_fv_typ_rec is_fv_kind y t
  | Record m | BaseRecord m ->
      Label.Map.exists
        (fun _lab t -> is_fv_typ_rec is_fv_kind y t)
        m

(* closing recursion *)
let rec is_fv_typ y t = is_fv_typ_rec is_fv_kind y t
and is_fv_kind y k = is_fv_kind_rec is_fv_typ y k

let is_fv = is_fv_typ


(* smart constructors *)
  let mkVar x = FVar x

  let mkApp t1 t2 = App(t1, t2)

  let mkLam x tau t =
    let y = h_typ x.content t in
    Lam (locate_with y x, tau, subst t x.content (BVar y))

  let mkRecord m = Record m

  let mkProj t l = Proj(t, l)

  let mkBaseForall x k t =
    let y = h_typ x.content t in
    BaseForall (locate_with y x, k, subst t x.content (BVar y))

  let mkBaseExists x k t =
    let y = h_typ x.content t in
    BaseExists (locate_with y x, k, subst t x.content (BVar y))

  let mkBaseRecord m = BaseRecord m

  let mkBaseArrow t1 t2 = BaseArrow(t1, t2)
end

module Kind = struct
  type 'a kind = 'a Typ.kind =
    | Base
    | Pi of Typ.Var.bound * 'a kind * 'a kind
    | Sigma of (Typ.Var.bound * 'a kind) Label.AList.t
    | Single of 'a * 'a kind

  type t = Typ.t kind

  let bvar_occurs x _k = not (Typ.Var.bequal x Typ.Var.bzero)
      (* from Sato-Pollack, x is free iff it is not 0 *)

  let bvar_occurs_field = bvar_occurs

  let var_map = Typ.var_map_kind

  let subst k x u =
    var_map
      (fun y -> if Typ.Var.equal x y then u else Typ.FVar y)
      k

  let subst_fields f x u =
    Label.AList.map (fun (y, k) -> (y, subst k x u)) f

  let bsubst k x u =
    if bvar_occurs x k
    then Typ.bsubst_kind k x u
    else k

  let bsubst_fields f x u =
    if bvar_occurs_field x f
    then Typ.bsubst_kind_fields bsubst f x u
    else f

  let equal = Typ.equal_kind

  let fv = Typ.fv_kind

  let is_fv = Typ.is_fv_kind

  let mkBase = Base

  let mkSingle t k = Single(t, k)

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
    | Lam of Var.bound located * Typ.typ * term
    | Let of Var.bound located * term * term
    | Record of term Label.AList.t
    | Proj of term * Label.t located
    | Gen of Typ.Var.bound located * (Typ.typ Typ.kind) located * term
    | Inst of term * Typ.typ
    | Fix of Var.bound located * Typ.t * term
    | Annot of term * Typ.t
    | Ex of Typ.Var.bound located * Kind.t located * term
    | Nu of Typ.Var.bound located * Kind.t located * term
    | Open of Typ.t * term (* the first argument is always a variable! *)
    | Sigma of
        Typ.t * Typ.Var.bound located * Kind.t located * Typ.t * term
          (* the first argument is always a variable! *)

  type t = term

  let term_bvar_occurs x _t = not (Var.bequal x Var.bzero)
      (* from Sato-Pollack, x is free iff it is not 0 *)
  let typ_bvar_occurs x _t = not (Typ.Var.bequal x Typ.Var.bzero)
      (* from Sato-Pollack, x is free iff it is not 0 *)

  let h_term_max f m =
    Label.AList.fold (fun _lab x acc -> Var.bmax (f x) acc) m Var.bzero

  let h_typ_max f m =
    Label.AList.fold (fun _lab x acc -> Typ.Var.bmax (f x) acc) m Typ.Var.bzero

  let h_ty_binder y h =
    if Typ.Var.bequal h Typ.Var.bzero
    then h
    else Typ.Var.bmax h (Typ.Var.bsucc y)

  let h_te_binder y h =
    if Var.bequal h Var.bzero
    then h
    else Var.bmax h (Var.bsucc y)

  let rec pre_h_term_var (x : Var.free) = function
    | FVar y -> if Var.equal x y then Var.bone else Var.bzero
    | BVar _ -> Var.bzero
    | App (t,u) -> Var.bmax (h_term_var x t) (h_term_var x u)
    | Lam (y, _tau, t) | Fix(y, _tau, t) ->
        h_te_binder y.content (h_term_var x t)
    | Let (y, t1, t2) ->
        Var.bmax (h_term_var x t1) (h_te_binder y.content (h_term_var x t2))
    | Proj(t, _) | Inst(t, _) | Gen (_, _, t) | Annot(t, _)
    | Sigma (_, _, _, _, t) | Open (_, t) | Nu (_, _, t) | Ex (_, _, t) ->
        h_term_var x t
    | Record m -> h_term_max (h_term_var x) m
  and h_term_var (x : Var.free) t =
    pre_h_term_var x t.content

  let rec pre_h_typ_var (x : Typ.Var.free) = function
    | FVar _ | BVar _ -> Typ.Var.bzero
    | App (t,u) | Let (_, t, u) ->
        Typ.Var.bmax (h_typ_var x t) (h_typ_var x u)
    | Lam (_, tau, t) | Inst(t, tau) | Fix(_, tau, t) | Annot(t, tau) ->
        Typ.Var.bmax (Typ.h_typ x tau) (h_typ_var x t)
    | Gen (y, k, t) | Nu (y, k, t) | Ex (y, k, t) ->
        Typ.Var.bmax (Typ.h_kind x k.content)
          (h_ty_binder y.content (h_typ_var x t))
    | Proj(t, _) -> h_typ_var x t
    | Record m -> h_typ_max (h_typ_var x) m
    | Sigma (y, z, k, tau, t) ->
        Typ.Var.bmax
          (Typ.h_typ x y)
          (Typ.Var.bmax
             (Typ.h_kind x k.content)
             (Typ.Var.bmax
                (Typ.h_typ x tau)
                (h_ty_binder z.content (h_typ_var x t))))
    | Open (y, t) ->
        Typ.Var.bmax
          (Typ.h_typ x y)
          (h_typ_var x t) 
          
  and h_typ_var (x : Typ.Var.free) t =
    pre_h_typ_var x t.content

  let rec pre_var_map_term_var f_free = function
    | FVar x -> f_free x
    | (BVar _) as b -> b
    | App (t1, t2) ->
        App(var_map_term_var f_free t1,
            var_map_term_var f_free t2)
    | Lam (x, k, t) ->
        Lam (x, k, var_map_term_var f_free t)
    | Let (x, t1, t2) ->
        Let (x, var_map_term_var f_free t1, var_map_term_var f_free t2)
    | Record m ->
        Record (Label.AList.map (var_map_term_var f_free) m)
    | Proj (t, lab) ->
        Proj(var_map_term_var f_free t, lab)
    | Gen (x, k, t) ->
        Gen (x, k, var_map_term_var f_free t)
    | Inst(t, tau) ->
        Inst (var_map_term_var f_free t, tau)
    | Fix (x, k, t) ->
        Fix (x, k, var_map_term_var f_free t)
    | Annot(t, tau) ->
        Annot (var_map_term_var f_free t, tau)
    | Sigma (x, y, k, tau, t) ->
        Sigma (x, y, k, tau, var_map_term_var f_free t)
    | Open (x, t) ->
        Open (x, var_map_term_var f_free t)
    | Nu (x, k, t) ->
        Nu (x, k, var_map_term_var f_free t)
    | Ex (x, k, t) ->
        Ex (x, k, var_map_term_var f_free t)
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
        Lam (x, Typ.var_map_typ f_free k, var_map_typ_var f_free t)
    | Let (x, t1, t2) ->
        Let (x, var_map_typ_var f_free t1, var_map_typ_var f_free t2)
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
    | Fix (x, k, t) ->
        Fix (x, Typ.var_map_typ f_free k, var_map_typ_var f_free t)
    | Annot(t, tau) ->
        Annot (var_map_typ_var f_free t,
               Typ.var_map_typ f_free tau)
    | Sigma (x, y, k, tau, t) ->
        Sigma (Typ.var_map_typ f_free x,
               y,
               { k with content = Typ.var_map_kind f_free k.content },
               Typ.var_map_typ f_free tau,
               var_map_typ_var f_free t)
    | Open (x, t) ->
        Open (Typ.var_map_typ f_free x,
              var_map_typ_var f_free t)
    | Nu (x, k, t) ->
        Nu (x,
            { k with content = Typ.var_map_kind f_free k.content },
            var_map_typ_var f_free t)
    | Ex (x, k, t) ->
        Ex (x,
            { k with content = Typ.var_map_kind f_free k.content },
            var_map_typ_var f_free t)
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
      if Var.bequal x y.content
      then Lam(y, k, t)
      else Lam (y, k, bsubst_term_var t x u)
  | Let (y, t1, t2) ->
      let t1' = bsubst_term_var t1 x u in
      if Var.bequal x y.content
      then Let (y, t1', t2)
      else Let (y, t1', bsubst_term_var t2 x u)
  | Record m ->
      Record (Label.AList.map (fun t -> bsubst_term_var t x u) m)
  | Proj (t, lab) ->
      Proj(bsubst_term_var t x u, lab)
  | Gen (y, k, t) ->
      Gen (y, k, bsubst_term_var t x u)
  | Inst (t, tau) ->
      Inst (bsubst_term_var t x u, tau)
  | Fix (y, k, t) ->
      if Var.bequal x y.content
      then Fix(y, k, t)
      else Fix (y, k, bsubst_term_var t x u)
  | Annot (t, tau) ->
      Annot (bsubst_term_var t x u, tau)
  | Sigma (y, z, k, tau, t) ->
      Sigma (y, z, k, tau, bsubst_term_var t x u)
  | Open (y, t) ->
      Open (y, bsubst_term_var t x u)
  | Nu (y, k, t) ->
      Nu (y, k, bsubst_term_var t x u)
  | Ex (y, k, t) ->
      Ex (y, k, bsubst_term_var t x u)
  and bsubst_term_var t x u =
    { t with
      content = pre_bsubst_term_var t.content x u }

  let bsubst_term_var t x u =
    if term_bvar_occurs x t
    then bsubst_term_var t x u
    else t

  let rec pre_bsubst_typ_var t x u = match t with
  | FVar _ | BVar _ -> t
  | App (t1, t2) ->
      App(bsubst_typ_var t1 x u,
          bsubst_typ_var t2 x u)
  | Lam (y, tau, t) ->
      Lam (y, Typ.bsubst_typ tau x u, bsubst_typ_var t x u)
  | Let (y, t1, t2) ->
      Let (y, bsubst_typ_var t1 x u, bsubst_typ_var t2 x u)
  | Record m ->
      Record (Label.AList.map (fun t -> bsubst_typ_var t x u) m)
  | Proj (t, lab) ->
      Proj(bsubst_typ_var t x u, lab)
  | Gen(y, k, t) ->
      let k' = { k with content = Typ.bsubst_kind k.content x u } in
      if Typ.Var.bequal x y.content
      then Gen(y, k', t)
      else Gen (y, k', bsubst_typ_var t x u)
  | Inst(t, tau) ->
      Inst(bsubst_typ_var t x u, Typ.bsubst_typ tau x u)
  | Fix (y, tau, t) ->
      Fix (y, Typ.bsubst_typ tau x u, bsubst_typ_var t x u)
  | Annot(t, tau) ->
      Annot(bsubst_typ_var t x u, Typ.bsubst_typ tau x u)
  | Sigma (y, z, k, tau, t) ->
      Sigma (Typ.bsubst_typ y x u,
             z,
             { k with content = Typ.bsubst_kind k.content x u },
             Typ.bsubst_typ tau x u,
             if Typ.Var.bequal x z.content then t else bsubst_typ_var t x u)
  | Open (y, t) ->
      Open (Typ.bsubst_typ y x u,
            bsubst_typ_var t x u)
  | Nu (y, k, t) ->
      Nu (y,
          { k with content = Typ.bsubst_kind k.content x u },
          if Typ.Var.bequal x y.content then t else bsubst_typ_var t x u)
  | Ex (y, k, t) ->
      Ex (y,
          { k with content = Typ.bsubst_kind k.content x u },
          if Typ.Var.bequal x y.content then t else bsubst_typ_var t x u)

  and bsubst_typ_var t x u =
    { t with
      content = pre_bsubst_typ_var t.content x u }

  let bsubst_typ_var t x u =
    if typ_bvar_occurs x t
    then bsubst_typ_var t x u
    else t

  let rec equal t1 t2 = pre_equal t1.content t2.content
  and pre_equal t1 t2 = match (t1, t2) with
  | (FVar x, FVar x') -> Var.equal x x'
  | (BVar x, BVar x') -> Var.bequal x x'
  | (Lam(x,tau,t), Lam(x',tau',t')) | (Fix(x,tau,t), Fix(x',tau',t')) ->
      Var.bequal x.content x'.content && Typ.equal_typ tau tau' && equal t t'
  | (Let(x,t1,t2), Let(x',t1',t2')) ->
      Var.bequal x.content x'.content && equal t1 t1' && equal t2 t2'
  | (App(t1,t2), App(t1',t2')) ->
      equal t1 t1' && equal t2 t2'
  | (Record m, Record m') ->
      Label.AList.equal equal m m'
  | (Proj(t,lab), Proj(t',lab')) ->
      equal t t' && Label.equal lab.content lab'.content
  | (Gen(x,k,t), Gen(x',k',t')) | (Nu(x,k,t), Nu(x',k',t'))
  | (Ex(x,k,t), Ex(x',k',t')) ->
      Typ.Var.bequal x.content x'.content &&
      Typ.equal_kind k.content k'.content && equal t t'
  | (Inst(t,tau), Inst(t',tau')) | (Annot(t,tau), Annot(t',tau')) ->
      equal t t' && Typ.equal_typ tau tau'
  | (Open(x,t), Open(x',t')) ->
      Typ.equal_typ x x' && equal t t'
  | (Sigma(y,x,k,tau,t), Sigma(y',x',k',tau',t')) ->
      Typ.equal_typ y y' && Typ.Var.bequal x.content x'.content
        && Typ.equal_kind k.content k'.content
        && Typ.equal_typ tau tau' && equal t t'
  | ((FVar _ | BVar _ | Lam(_,_,_) | Record _ | Proj(_,_) |
    Gen(_,_,_) | App(_,_) | Let(_,_,_) | Inst(_,_) | Fix(_,_,_) | Annot(_,_) |
    Sigma(_,_,_,_,_) | Open(_,_) | Ex(_,_,_) | Nu(_,_,_)),_) ->
      false

  let rec fv_typ t = let open Typ.Var.Set in
  match t.content with
  | BVar _ | FVar _ -> empty
  | App(e1, e2) | Let(_, e1, e2) -> union (fv_typ e1) (fv_typ e2)
  | Lam(_, t, e) | Inst(e, t) | Fix(_, t, e) | Annot(e, t) | Open(t, e) ->
      union (Typ.fv t) (fv_typ e)
  | Proj(e, _) -> fv_typ e
  | Nu(_, k, e) | Ex(_, k, e) | Gen(_, k, e) ->
      union (Kind.fv k.content) (fv_typ e)
  | Sigma(b, _, k, t, e) ->
      union (Typ.fv b)
        (union (Kind.fv k.content)
           (union (Typ.fv t) (fv_typ e)))
  | Record m ->
      Label.AList.fold
        (fun _lab e acc -> union (fv_typ e) acc)
        m empty

  let rec is_fv_typ y t = match t.content with
  | BVar _ | FVar _ -> false
  | App(e1, e2) | Let(_, e1, e2) -> (is_fv_typ y e1) || (is_fv_typ y e2)
  | Lam(_, t, e) | Inst(e, t) | Fix(_, t, e) | Annot(e, t) | Open(t, e) ->
      (Typ.is_fv y t) || (is_fv_typ y e)
  | Proj(e, _) -> is_fv_typ y e
  | Nu(_, k, e) | Ex(_, k, e) | Gen(_, k, e) ->
      (Kind.is_fv y k.content) || (is_fv_typ y e)
  | Sigma(b, _, k, t, e) ->
      (Typ.is_fv y b) || (Kind.is_fv y k.content) ||
      (Typ.is_fv y t) || (is_fv_typ y e)
  | Record m ->
      Label.AList.exists
        (fun _lab e -> is_fv_typ y e)
        m

  let rec fv_term t = let open Var.Set in
  match t.content with
  | BVar _ -> empty
  | FVar x -> singleton x
  | App(e1, e2) | Let(_, e1, e2) -> union (fv_term e1) (fv_term e2)
  | Lam(_, _, e) | Inst(e, _) | Fix(_, _, e) | Annot(e, _) |
    Open(_, e) | Proj(e, _) | Nu(_, _, e) | Ex(_, _, e) |
    Gen(_, _, e) | Sigma(_, _, _, _, e) ->
      fv_term e
  | Record m ->
      Label.AList.fold
        (fun _lab e acc -> union (fv_term e) acc)
        m empty

  let rec is_fv_term y t = match t.content with
  | BVar _ -> false
  | FVar x -> Var.equal y x
  | App(e1, e2) | Let(_, e1, e2) -> (is_fv_term y e1) || (is_fv_term y e2)
  | Lam(_, _, e) | Inst(e, _) | Fix(_, _, e) | Annot(e, _) |
    Open(_, e) | Proj(e, _) | Nu(_, _, e) | Ex(_, _, e) |
    Gen(_, _, e) | Sigma(_, _, _, _, e) ->
      is_fv_term y e
  | Record m ->
      Label.AList.exists
        (fun _lab e -> is_fv_term y e)
        m

(* smart constructors *)
  let mkVar x = FVar x

  let mkLam x tau t =
    let y = h_term_var x.content t in
    Lam (locate_with y x, tau, subst_term_var t x.content (BVar y))

  let mkApp t1 t2 = App(t1, t2)

  let mkLet x t1 t2 =
    let y = h_term_var x.content t2 in
    Let (locate_with y x, t1, subst_term_var t2 x.content (BVar y))

  let mkRecord m = Record m

  let mkProj t lab = Proj(t, lab)

  let mkGen x k t =
    let y = h_typ_var x.content t in
    Gen (locate_with y x, k, subst_typ_var t x.content (Typ.BVar y))

  let mkInst t tau = Inst(t, tau)

  let mkFix x tau t =
    let y = h_term_var x.content t in
    Fix (locate_with y x, tau, subst_term_var t x.content (BVar y))

  let mkAnnot t tau = Annot(t, tau)

  let mkEx x k t =
    let y = h_typ_var x.content t in
    Ex (locate_with y x, k, subst_typ_var t x.content (Typ.BVar y))

  let mkNu x k t =
    let y = h_typ_var x.content t in
    Nu (locate_with y x, k, subst_typ_var t x.content (Typ.BVar y))

  let mkOpen x t =
    Open (map Typ.mkVar x, t)

  let mkSigma x y k tau t =
    let z = h_typ_var y.content t in
    Sigma (map Typ.mkVar x,
           locate_with z y, k, tau, subst_typ_var t y.content (Typ.BVar z))

end

module Prog = struct
  type req =
    | RequireVal of Term.Var.free located * Typ.t
    | RequireTyp of Typ.Var.free located * Kind.t located
    | ExportTyp of Typ.Var.free located * Kind.t located
  type reqs = req list

  type t = { reqs : reqs ; code : Term.t }

end
