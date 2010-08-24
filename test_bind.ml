open Binder

module Var : F_ATOM_IMPL = struct
  type t = string
  let eq x y = String.compare x y = 0
  let fresh =
    let i = ref 0 in fun () ->
      let n = !i in incr i; ("x_" ^ (string_of_int n))
  let to_string x = x
end

module TeVar = Make(Var)

type term =
  | Var of TeVar.atom
  | App of term * term
  | Lam of term TeVar.abs

let rec subst t x u = match t with
| Var y -> if TeVar.eq x y then u else t
| App(t1, t2) -> App(subst t1 x u, subst t2 x u)
| Lam abs -> Lam (TeVar.Abs.subst subst abs x u)

let rec rename t x y = match t with
| Var z -> if TeVar.eq x z then Var y else t
| App(t1, t2) -> App(rename t1 x y, rename t2 x y)
| Lam abs -> Lam (TeVar.Abs.rename rename abs x y)

let rec bsubst t x u = match t with
| Var y -> if TeVar.beq x y then u else t
| App(t1, t2) -> App(bsubst t1 x u, bsubst t2 x u)
| Lam abs -> Lam (TeVar.Abs.bsubst bsubst abs x u)

let rec brename t x y = match t with
| Var z -> if TeVar.beq x z then Var y else t
| App(t1, t2) -> App(brename t1 x y, brename t2 x y)
| Lam abs -> Lam (TeVar.Abs.brename brename abs x y)

let rec h x = function
  | Var y -> TeVar.h x y
  | App(t1, t2) -> TeVar.max (h x t1) (h x t2)
  | Lam abs -> TeVar.Abs.h h x abs

let make_abs = TeVar.Abs.make h rename
let mkLam x t = Lam (make_abs x t)

let inst = TeVar.Abs.inst bsubst

let destruct_abs = TeVar.Abs.destruct brename

let rec eq t t' = match (t, t') with
| (Var x, Var x') -> TeVar.eq x x'
| (App(t1, t2), App(t1', t2')) -> eq t1 t1' && eq t2 t2'
| (Lam abs, Lam abs') -> TeVar.Abs.eq eq abs abs'
| _ -> false

let is_lam = function
  | Lam _ -> true
  | _ -> false

(* weak head normal form *)
let rec whnf = function
  | Var _ | Lam _ as t -> t
  | App(t, u) ->
      begin
        match whnf t with
        | Lam abs -> whnf (inst abs u)
        | t' -> App(t', u)
      end

(* normal form *)
let rec nf t =
  match whnf t with
  | Var _ as t -> t
  | App(t, u) ->
      assert (not (is_lam t)) ;
      App(t, nf u)
  | Lam abs ->
      let (x, t) = destruct_abs abs in
      mkLam x (nf t)
