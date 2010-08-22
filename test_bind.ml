open Bind

type te

module FAtomImpl = struct
  type sort = te
  type 'sort t = string constraint 'sort = sort
  let eq (x : string) (y: string) = x = y
  let fresh =
    let r = ref 0 in fun () ->
      let n = !r in
      incr r ; Printf.sprintf "x__%i" n
end

module BAtomImpl = struct
  type sort = te
  type 'sort t = int constraint 'sort = sort
  let zero = 0
  let succ x = x + 1
  let max (x : int) (y: int) = max x y
  let eq (x : int) (y: int) = x = y
end

module Atom = Make(FAtomImpl)(BAtomImpl)

type term =
  | FVar of te Atom.free
  | BVar of te Atom.bound
  | App of term * term
  | Lam of (te, term) Atom.Abs.t

let rec var_map f = function
  | FVar x -> f x
  | BVar _ as t -> t
  | App (t, u) -> App(var_map f t, var_map f u)
  | Lam abs -> Lam (Atom.Abs.map (var_map f) abs)

let rec hom_rec f_abs f_free f_bound f_app f_lam t = match t with
| FVar x -> f_free x
| BVar x -> f_bound x
| App(t, u) ->
    f_app
      (hom_rec f_abs f_free f_bound f_app f_lam t)
      (hom_rec f_abs f_free f_bound f_app f_lam u)
| Lam abs ->
    f_lam (f_abs abs)

let fsubst t x u =
  var_map (fun y -> if Atom.F.eq x y then u else FVar y) t

let rec bsubst t =
  hom_rec
    (Atom.Abs.mk_bsubst bsubst)
    (fun y _ _ -> FVar y)
    (fun y x u -> if Atom.B.eq y x then u else BVar y)
    (fun t1 t2 x u -> App(t1 x u, t2 x u))
    (fun abs x u -> Lam (abs x u))
    t
