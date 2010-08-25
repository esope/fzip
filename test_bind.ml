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

let rec var_map f = function
  | Var x -> f x
  | App(t, u) -> App(var_map f t, var_map f u)
  | Lam abs -> Lam (TeVar.Abs.var_map var_map f abs)

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
let rec nf strong t =
  match whnf t with
  | Var _ as t -> t
  | App(t, u) ->
      assert (not (is_lam t)) ;
      App(t, nf strong u)
  | Lam abs as t ->
      if strong
      then
        let (x, t) = destruct_abs abs in
        mkLam x (nf strong t)
      else t

let weak_nf = nf false
let nf = nf true

(* Church's encodings *)
(* Taken from http://en.wikipedia.org/wiki/Church_encoding *)

let fix = (* λf. (λx. f (λy. x x y)) (λx. f (λy. x x y)) *)
  let f = TeVar.fresh ()
  and x = TeVar.fresh ()
  and y = TeVar.fresh () in
  mkLam f
    (App(mkLam x
           (App(Var f,
                mkLam y (App(App(Var x, Var x), Var y)))),
         mkLam x
           (App(Var f,
                mkLam y (App(App(Var x, Var x), Var y))))))
(*
let fix = (* λf.(λx.f (x x)) (λx.f (x x)) *)
  let f = TeVar.fresh ()
  and x = TeVar.fresh () in
  mkLam f (App(mkLam x (App(Var f, App(Var x, Var x))),
               mkLam x (App(Var f, App(Var x, Var x)))))
*)

(* booleans *)
let bool_true = (* λa.λb. a *)
  let a = TeVar.fresh ()
  and b = TeVar.fresh () in
  mkLam a (mkLam b (Var a))

let bool_false = (* λa.λb. b *)
  let a = TeVar.fresh ()
  and b = TeVar.fresh () in
  mkLam a (mkLam b (Var b))

let bool_and = (* λm.λn. m n m *)
  let m = TeVar.fresh ()
  and n = TeVar.fresh () in
  mkLam m (mkLam n (App(App(Var m, Var n), Var m)))

let bool_or = (* λm.λn. m m n *)
  let m = TeVar.fresh ()
  and n = TeVar.fresh () in
  mkLam m (mkLam n (App(App(Var m, Var m), Var n)))

let bool_not = (* λm.λa.λb. m b a *)
  let m = TeVar.fresh ()
  and a = TeVar.fresh ()
  and b = TeVar.fresh () in
  mkLam m (mkLam a (mkLam b (App(App(Var m, Var b), Var a))))

let bool_xor = (* λm.λn.λa.λb. m (n b a) (n a b) *)
  let m = TeVar.fresh ()
  and n = TeVar.fresh ()
  and a = TeVar.fresh ()
  and b = TeVar.fresh () in
  mkLam m (mkLam n (mkLam a (mkLam b (App(App(Var m, Var b), Var a)))))

(* natural numbers *)
let int =
  let rec make_app n a b =
    if n = 0 then b
    else App(a, make_app (n-1) a b)
  in
  let f = TeVar.fresh () and x = TeVar.fresh () in fun n ->
  mkLam f (mkLam x (make_app n (Var f) (Var x)))

let plus = (* λm.λn.λf.λx. m f (n f x) *)
  let m = TeVar.fresh ()
  and n = TeVar.fresh ()
  and f = TeVar.fresh ()
  and x = TeVar.fresh () in
  mkLam m
    (mkLam n
       (mkLam f
          (mkLam x
             (App(App(Var m, Var f),
                  App(App(Var n, Var f),
                      Var x))))))

let succ = (* λn.λf.λx. f (n f x) *)
  let n = TeVar.fresh ()
  and f = TeVar.fresh ()
  and x = TeVar.fresh () in
  mkLam n
    (mkLam f
       (mkLam x
          (App(Var f,
               App(App(Var n, Var f),
                   Var x)))))

let mult = (* λm.λn.λf. n (m f) *)
  let m = TeVar.fresh ()
  and n = TeVar.fresh ()
  and f = TeVar.fresh () in
  mkLam m
    (mkLam n
       (mkLam f
          (App(Var n, App(Var m, Var f)))))
  
let exp = (* λm.λn. n m *)
  let m = TeVar.fresh ()
  and n = TeVar.fresh () in
  mkLam m
    (mkLam n
       (App(Var n, Var m)))

let pred = (* λn.λf.λx. n (λg.λh. h (g f)) (λu. x) (λu. u) *)
  let n = TeVar.fresh ()
  and f = TeVar.fresh ()
  and x = TeVar.fresh ()
  and g = TeVar.fresh ()
  and h = TeVar.fresh ()
  and u = TeVar.fresh () in
  mkLam n
    (mkLam f
       (mkLam x 
          (App(App(App(Var n,
                       mkLam g
                         (mkLam h
                            (App(Var h, App(Var g, Var f))))),
                   mkLam u (Var x)),
              mkLam u (Var u)))))

let sub = (* λm.λn. (n pred) m *)
  let m = TeVar.fresh ()
  and n = TeVar.fresh () in
  mkLam m (mkLam n (App(App(Var n, pred), Var m)))
  
let is_zero = (* λn. n (λx.false) true *)
  let n = TeVar.fresh ()
  and x = TeVar.fresh () in
  mkLam n (App(App(Var n, mkLam x bool_false), bool_true))

let fact = (* fix (λfact λn. is_zero n 1 (mult n (fact (pred n)))) *)
  let fact = TeVar.fresh ()
  and n = TeVar.fresh () in
  App(fix,
      mkLam fact
        (mkLam n
           (App(App(App(is_zero, Var n), int 1),
                App(App(mult, Var n),
                    App(Var fact, App(pred, Var n)))))))

(* pairs *)
let pair = (* λx.λy.λz.z x y *)
  let x = TeVar.fresh ()
  and y = TeVar.fresh ()
  and z = TeVar.fresh () in
  mkLam x (mkLam y (mkLam z (App(App(Var z, Var x), Var y))))

let pair_fst = (* λp.p (λx.λy.x) *)
  let p = TeVar.fresh () 
  and x = TeVar.fresh ()
  and y = TeVar.fresh () in
  mkLam p (App(Var p, mkLam x (mkLam y (Var x))))

let pair_snd = (* λp.p (λx.λy.y) *)
  let p = TeVar.fresh () 
  and x = TeVar.fresh ()
  and y = TeVar.fresh () in
  mkLam p (App(Var p, mkLam x (mkLam y (Var y))))

(* lists *)
let list_nil = (* λc.λn.n *)
  let c = TeVar.fresh () 
  and n = TeVar.fresh () in
  mkLam c (mkLam n (Var n))

let list_isnil = (* λl.l (λh.λt.false) true *)
  let l = TeVar.fresh () 
  and h = TeVar.fresh ()
  and t = TeVar.fresh () in
  mkLam l (App(App(Var l, mkLam h (mkLam t bool_false)), bool_true))

let list_cons = (* λh.λt.λc.λn.c h (t c n) *)
  let h = TeVar.fresh ()
  and t = TeVar.fresh ()
  and c = TeVar.fresh ()
  and n = TeVar.fresh () in
  mkLam h
    (mkLam t
       (mkLam c
          (mkLam n
             (App(App(Var c, Var h), App(App(Var t, Var c), Var n))))))

let list_head = (* λl.l (λh.λt.h) false *)
  let l = TeVar.fresh () 
  and h = TeVar.fresh ()
  and t = TeVar.fresh () in
  mkLam l (App(App(Var l, mkLam h (mkLam t (Var h))), bool_false))

let list_tail =
(* λl.fst (l (λx.λp.pair (snd p) (cons x (snd p))) (pair nil nil)) *)
  let l = TeVar.fresh () 
  and x = TeVar.fresh ()
  and p = TeVar.fresh () in
  mkLam l
    (App(pair_fst,
        App(App(Var l,
               mkLam x
                  (mkLam p
                     (App(App(pair,
                              App(pair_snd, Var p)),
                         App(App(list_cons,
                                 Var x),
                             App(pair_snd, Var p)))))),
            App(App(pair, list_nil), list_nil))))


(* some tests *)
let () =
  Printf.printf "42 + 12 = 54? %b\n%!"
    (eq (nf (App(App(plus, int 42), (int 12)))) (nf (int 54)))

let () =
  Printf.printf "42 * 12 = 504? %b\n%!"
    (eq (nf (App(App(mult, int 42), (int 12)))) (nf (int 504)))

let () =
  Printf.printf "2 ^ 12 = 4096? %b\n%!"
    (eq (nf (App(App(exp, int 2), (int 12)))) (nf (int 4096)))

let () =
  Printf.printf "2 ^ 16 = 65536? %b\n%!"
    (eq (nf (App(App(exp, int 2), (int 16)))) (nf (int 65536)))

let () =
  Printf.printf "is_zero 0 = true? %b\n%!"
    (eq (nf (App(is_zero, int 0))) (nf bool_true))

let () =
  Printf.printf "is_zero 42 = false? %b\n%!"
    (eq (nf (App(is_zero, int 42))) (nf bool_false))

let () =
  Printf.printf "fact 0 = 1? %b\n%!"
    (eq (nf (App(fact, int 0))) (nf (int 1)))

let () =
  Printf.printf "fact 8 = 40320? %b\n%!"
    (eq (nf (App(fact, int 8))) (nf (int 40320)))

let () =
  Printf.printf "and true false = false? %b\n%!"
    (eq (nf (App(App(bool_and, bool_true), bool_false))) (nf bool_false))

let () =
  Printf.printf "or true false = true? %b\n%!"
    (eq (nf (App(App(bool_or, bool_true), bool_false))) (nf bool_true))

let () =
  Printf.printf "not true = false? %b\n%!"
    (eq (nf (App(bool_not, bool_true))) (nf bool_false))

let () =
  Printf.printf "fst (pair 0 1) = 0? %b\n%!"
    (eq (nf (App(pair_fst, App(App(pair, int 0), int 1)))) (nf (int 0)))

let () =
  Printf.printf "snd (pair 0 1) = 0? %b\n%!"
    (eq (nf (App(pair_snd, App(App(pair, int 0), int 1)))) (nf (int 1)))

let time f x =
  let start = Unix.gettimeofday () in
  let result = f x in
  let stop = Unix.gettimeofday () in
  Printf.printf "Time: %fs.\n%!" (stop -. start) ;
  result

(* SECD abstract machine *)
type stack_elem = Cl of env * term
and env = (TeVar.atom * stack_elem) list
type stack = stack_elem list
type control_elem = CTe of term | CApp
type control = control_elem list
type dump = DNil | DState of secd
and secd = stack * env * control * dump

let rec secd = function
  | (s, e, CTe (Var x) :: c, d) ->
      secd (List.assoc x e :: s, e, c, d)
  | (s, e, CTe (Lam _ as t) :: c, d) ->
      secd (Cl (e, t) :: s, e, c, d)
  | (s, e, CTe (App(t, u)) :: c, d) ->
      secd (s, e, CTe t :: CTe u :: CApp :: c, d)
  | (Cl (e', Lam a) :: clos :: s, e, CApp :: c, d) ->
      let (x, t) = destruct_abs a in
      secd ([], (x, clos) :: e', [CTe t], DState (s, e, c, d))
  | (clos :: s, e, [], DState(s',e',c',d')) ->
      secd (clos :: s', e', c', d')
  | s -> s

let term_to_dump t = ([], [], [CTe t], DNil)
let rec readback e =
  var_map (fun x ->
    try
      let Cl (e', t') = List.assoc x e in
      readback e' t'
    with Not_found -> Var x)

let eval t =
  match secd (term_to_dump t) with
  | ([Cl (e', t)], [], [], DNil)  -> readback e' t
  | _ -> assert false
(* secd is fast, but readback is very slow *)  

let () =
  Printf.printf "Computing (weak_nf (fact 170000))... \n%!" ;
  ignore (time weak_nf (App(fact, int 170000))) ;
  Printf.printf "Done.\n%!" ;
  Printf.printf "Computing (eval (fact 170000))... \n%!" ;
  ignore (time eval (App(fact, int 170000))) ;
  Printf.printf "Done.\n%!"
