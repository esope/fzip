open Ast.Typ
open Ast_utils
open Parser_utils
open OUnit
open Wftype

(* tests about wftype *)
let test_wftype ~t ~k =
  (Printf.sprintf "⊢ %s :: %s ?" t k) >:: (fun () ->
    let t = String.parse_typ t
    and k = String.parse_kind k in
    assert_equal
      ~printer:PPrint.Kind.string
      ~cmp:(wfsub Env.empty) (wftype Env.empty t) k)

let tests_wftype = "Tests about wftype" >:::
  [
   test_wftype ~t:"fun (x::*) x" ~k:"* => *" ;
   test_wftype ~t:"fun (x::*) fun (y::*=>*) y x" ~k:"* => (* => *) => *"
 ]

(* tests about normal forms and equivalence *)
let test_nf ~t ~nf () =
  let t = String.parse_typ t
  and nf = String.parse_typ nf in
  let nf_e =
    let k = wftype Env.empty t in
    Normalize.typ_norm Env.empty t k in
  assert_equal ~printer:PPrint.Typ.string ~cmp:eq_typ nf_e nf

let test_equiv ?(neg=false) ~env ~t ~u ~k () =
  TestCase (fun () ->
    assert_bool (Printf.sprintf "env ⊢ %s ≡ %s :: %s?" t u k)
      (let t = String.parse_typ t
      and u = String.parse_typ u
      and k = String.parse_kind k in
      let b = Normalize.equiv_typ env t u k in
      if neg then not b else b))

let mknum_string n =
  let rec mkapp_n t1 t2 = function
    | 0 -> Printf.sprintf "%s" t2
    | n -> Printf.sprintf "((%s) (%s))" t1 (mkapp_n t1 t2 (n-1))
  in
  Printf.sprintf "(λ(f :: ⋆ ⇒ ⋆) λ(x :: ⋆) %s)" (mkapp_n "f" "x" n)

let nat_string = "(* => *) => * => *"

let add_string = 
  ("(λ (n :: " ^ nat_string ^ ")" ^
   " λ (m :: " ^ nat_string ^ ")" ^
   " λ (f :: ⋆ ⇒ ⋆) λ (x :: ⋆) n f (m f x))")


let tests_nf = "Tests about normal forms and equivalence" >:::
  [
   (let f = "fun (x::*) fun (y:: * => *) y x" in
   ("nf of " ^ f) >:: test_nf ~t:f ~nf:f) ;

   "3 + 4 = 7?" >::
   test_nf ~t:(add_string ^ (mknum_string 3) ^ (mknum_string 4))
     ~nf:(mknum_string 7) ;

   "42 + 96 = 138?" >::
   test_nf ~t:(add_string ^ (mknum_string 42) ^ (mknum_string 96))
     ~nf:(mknum_string 138) ;

   "nf of fun (x::*) fun (y:: * => *) y x" >::
   test_nf ~t:"fun (x::*) fun (y:: * => *) y x"
     ~nf:"fun (x::*) fun (y:: * => *) y x" ;
   (let f = "λ(x :: ⋆ × ⋆ × (⋆ × ⋆ ⇒ ⋆ × ⋆)) x"
   and g =
     "λ(x :: ⋆ × ⋆ × (⋆ × ⋆ ⇒ ⋆ × ⋆))\
       < <x.fst.fst, x.fst.snd>,\
       λ(y:: ⋆×⋆) < (x.snd <y.fst,y.snd>).fst , (x.snd <y.fst,y.snd>).snd >>"
   in
   ("nf of " ^ f) >:: test_nf ~t:f ~nf:g) ;

   test_equiv
     ~neg:true
     ~env:(Env.empty)
     ~t:"λ (c :: *) λ (x :: *) c"
     ~u:"λ (c :: *) λ (x :: *) x"
     ~k:"* => * => *" () ;

   test_equiv
     ~env:(Env.empty)
     ~t:"λ (c :: *) λ (x :: *) c"
     ~u:"λ (c :: *) λ (x :: *) x"
     ~k:"Π(c :: *) S(c) => *" () ;

   (let env =
     Env.add_typ_var "f" (String.parse_kind "(* => *) => *")
       (Env.add_typ_var "c" (String.parse_kind "*") Env.empty) in
   test_equiv
     ~neg:true
     ~env
     ~t:"f (λ (x :: *) c)"
     ~u:"f (λ (x :: *) x)"
     ~k:"*" ()) ;

   (let env =
     Env.add_typ_var "f" (String.parse_kind "(S(c) => *) => *")
       (Env.add_typ_var "c" (String.parse_kind "*") Env.empty) in
   test_equiv
     ~env
     ~t:"f (λ (x :: *) c)"
     ~u:"f (λ (x :: *) x)"
     ~k:"*" ()) ;
 ]

(* tests about wfterm *)
let test_wfterm ~e ~t =
  (Printf.sprintf "⊢ %s : %s?" e t) >:: (fun () ->
    let e = String.parse_term e
    and t = String.parse_typ t in
    assert_equal
      ~printer:PPrint.Typ.string
      ~cmp:(Wfterm.wfsub Env.empty) (Wfterm.wfterm Env.empty e) t)

let tests_wfterm = "Tests about wfterm" >:::
  [
   test_wfterm ~e:"Fun (α:: *) fun (x : α) x"
     ~t:"∀ (a:: *) a -> a" ;

   test_wfterm ~e:"Fun (α:: *) fun (x : {α ; α}) x"
     ~t:"∀ (a:: *) {a;a} -> {a;a}" ;

   test_wfterm ~e:"Fun (α:: * => *) Fun (β :: *) fun (x : {α β ; α β}) x"
     ~t:"∀ (α:: *=>*) ∀ (β::*) {α β ; α β} -> {α β ; α β}" ;
 ]

(* all tests *)
let tests = TestList [ tests_wftype ; tests_nf ; tests_wfterm ]

(* running tests *)
let () =
  ignore (run_test_tt tests)
