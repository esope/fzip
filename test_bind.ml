open Bind

type te

module Build = struct
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
end
open Build.Atom

type term =
  | FVar of te free
  | BVar of te bound
  | App of term * term
  | Lam of (te, term) Abs.t

let rec var_fmap f = function
  | FVar x -> f x
  | BVar _ as t -> t
  | App (t, u) -> App(var_fmap f t, var_fmap f u)
  | Lam abs -> Lam (Abs.fmap (var_fmap f) abs)

let rec bsubst t x u = match t with
  | FVar y as t -> t
  | BVar y as t -> if Bound.eq x y then u else t
  | App(t1, t2) -> App(bsubst t1 x u, bsubst t2 x u)
  | Lam abs -> Lam (Abs.bmap bsubst abs x u)

let rec hom_rec f_abs f_free f_bound f_app f_lam t = match t with
| FVar x -> f_free x
| BVar x -> f_bound x
| App(t, u) ->
    f_app
      (hom_rec f_abs f_free f_bound f_app f_lam t)
      (hom_rec f_abs f_free f_bound f_app f_lam u)
| Lam abs ->
    f_lam (f_abs abs)

let rec hom_tree_rec f_abs f_free f_bound f_node =
  hom_rec f_abs f_free f_bound
    (fun t u -> f_node [t ; u])
    (fun abs -> f_node [abs])

let fsubst t x u =
  var_fmap (fun y -> if Free.eq x y then u else FVar y) t
let instantiate =
  Abs.mk_instantiate bsubst

