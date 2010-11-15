open Ast
open Ast_utils
open Parser_utils
open OUnit
open Wftype

(* tests about parsing *)
let test_kind_parser k1 k2 =
  ("Parsing " ^ k1) >:: (fun () ->
    let k1 = String.Kind.parse k1
    and k2 = String.Kind.parse k2 in
    assert_equal ~cmp:Kind.equal k1 k2)

let test_typ_parser t1 t2 =
  ("Parsing " ^ t1) >:: (fun () ->
    let t1 = String.Typ.parse t1
    and t2 = String.Typ.parse t2 in
    assert_equal ~cmp:Typ.equal t1 t2)

let test_term_parser t1 t2 =
  ("Parsing " ^ t1) >:: (fun () ->
    let t1 = String.Term.parse t1
    and t2 = String.Term.parse t2 in
    assert_equal ~cmp:Term.equal t1 t2)

let tests_parsing = "Tests about parsing" >:::
  [
   test_kind_parser "⋆" "*" ;
   test_kind_parser "* => *" "* ⇒ *" ;
   test_kind_parser "* => * => *" "* => (* => *)" ;
   test_kind_parser "Π (x :: *) => * => *" "Π (x :: *) => (* => *)" ;
   test_typ_parser "a -> a" "a → a" ;
   test_typ_parser "a -> a -> a" "a -> (a -> a)" ;
   test_typ_parser "{ val l1: a val l2: a }" "{ val l1: a val l2: a }" ;
   test_typ_parser "< type l1 = a type l2 = a >"
     "< type l1 = a type l2 = a >" ;
   test_typ_parser "λ (a :: *) → a b" "fun (a :: *) -> (a b)" ;
   test_typ_parser "λ (a :: *) → a . b" "λ (a :: *) → (a . b)" ;
   test_typ_parser "λ (a :: *) → a < type B=b type C=c>"
     "λ (a :: *) → (a < type B=b type C=c>)" ;
   test_typ_parser
     "λ (a :: *) →  a { val B: b val C: c }"
     "λ (a :: *) → (a { val B: b val C: c })" ;
   test_typ_parser "∀ (a :: *) a b" "forall (a :: *) (a b)" ;
   test_typ_parser "∀ (a :: *) a . b" "∀ (a :: *) (a . b)" ;
   test_typ_parser "∀ (a :: *) a < type B=b type C=c>"
     "∀ (a :: *) (a < type B=b type C=c>)" ;
   test_typ_parser
     "∀ (a :: *)  a { val B: b val C: c }"
     "∀ (a :: *) (a { val B: b val C: c })" ;
   test_term_parser "Λ(a::*) → λ(x:a) → x" "Fun(a::*) -> fun(x:a) -> x" ;
   test_term_parser "λ (a::*)(x:a) → x" "fun(a::*)(x:a) -> x" ;
   test_term_parser "λ(x:a) → x y" "λ(x:a) → (x y)" ;
   test_term_parser "λ(x:a) → x . y" "λ(x:a) → (x . y)" ;
   test_term_parser "Λ(a::*) → x y" "Λ(a::*) → (x y)" ;
   test_term_parser "Λ(a::*) → x . y" "Λ(a::*) → (x . y)" ;

 ]

(* tests about wftype *)
let test_wftype ~t ~k =
  (Printf.sprintf "⊢ %s :: %s ?" t k) >:: (fun () ->
    let t = String.Typ.parse t
    and k = String.Kind.parse k in
    assert_equal
      ~printer:PPrint.Kind.string
      ~cmp:(sub_kind_b Env.empty) (wftype Env.empty t) k)

let tests_wftype = "Tests about wftype" >:::
  [
   test_wftype ~t:"fun (x::*) → x" ~k:"* => *" ;
   test_wftype ~t:"fun (x::*) → fun (y::*=>*) → y x" ~k:"* => (* => *) => *" ;
   test_wftype ~t:"fun (x::*) → ∀ (y::*=>*) y x" ~k:"* => *" ;
   test_wftype ~t:"fun (x::*) → ∃ (y::*=>*) y x" ~k:"* => *" ;
   test_wftype
     ~t:"fun (x::<type A::* type B::*>) → < type C= x.A type D=x.B >"
     ~k:"< type A::* type B::* > => < type C::* type D::* >" ;
   test_wftype
     ~t:"fun (x::<type A::* type B::*>) → < type C= x.A type D=x.B >"
     ~k:"Π (x::< type A::* type B::* >) => < type C::S(x.A) type D::S(x.B) >" ;
   test_wftype
     ~t:"fun (x::<type A::* type B::*>) → < type A= x.A type B=x.B >"
     ~k:"Π (x :: < type A::* type B::* >) => S(x :: < type A::* type B::* >)" ;
   test_wftype
     ~t:"fun (x::<type A::* type B::*>) → < type A= x.A type B=x.B >"
     ~k:"Π (x :: < type A::* type B::* >) => S(x :: < type A::* >)" ;
   test_wftype
     ~t:"fun (x::<type A::* type B::*>) → < type A= x.A type B=x.B >"
     ~k:"Π (x :: < type A::* type B::* >) => S(x :: < type A::* >)" ;
   test_wftype
     ~t:"fun (x::<type A::* type B::*>) → < type A= x.A type B=x.B >"
     ~k:"Π (x :: < type A::* type B::* >) => S(x :: < >)" ;
 ]

(* tests about normal forms and equivalence *)
let test_nf ~t ~nf () =
  let t = String.Typ.parse t
  and nf = String.Typ.parse nf in
  let nf_e =
    let k = wftype Env.empty t in
    Normalize.typ_norm Env.empty t k in
  assert_equal ~printer:PPrint.Typ.string ~cmp:Typ.equal nf_e nf

let test_equiv ?(neg=false) ~env ~t ~u ~k () =
  TestCase (fun () ->
    assert_bool (Printf.sprintf "env ⊢ %s ≡ %s :: %s?" t u k)
      (let t = String.Typ.parse t
      and u = String.Typ.parse u
      and k = String.Kind.parse k in
      let b = Normalize.equiv_typ_b env t u k in
      if neg then not b else b))

let mknum_string n =
  let rec mkapp_n t1 t2 = function
    | 0 -> Printf.sprintf "%s" t2
    | n -> Printf.sprintf "((%s) (%s))" t1 (mkapp_n t1 t2 (n-1))
  in
  Printf.sprintf "(λ(f :: ⋆ ⇒ ⋆) → λ(x :: ⋆) → %s)" (mkapp_n "f" "x" n)

let nat_string = "(* => *) => * => *"

let add_string = 
  ("(λ (n :: " ^ nat_string ^ ") →" ^
   " λ (m :: " ^ nat_string ^ ") → " ^
   " λ (f :: ⋆ ⇒ ⋆) → λ (x :: ⋆) → n f (m f x))")


let tests_nf = "Tests about normal forms and equivalence" >:::
  [
   (let f = "fun (x::*) → fun (y:: * => *) → y x" in
   ("nf of " ^ f) >:: test_nf ~t:f ~nf:f) ;

   "3 + 4 = 7?" >::
   test_nf ~t:(add_string ^ (mknum_string 3) ^ (mknum_string 4))
     ~nf:(mknum_string 7) ;

   "42 + 96 = 138?" >::
   test_nf ~t:(add_string ^ (mknum_string 42) ^ (mknum_string 96))
     ~nf:(mknum_string 138) ;

   "nf of fun (x::*) → fun (y:: * => *) → y x" >::
   test_nf ~t:"fun (x::*) → fun (y:: * => *) → y x"
     ~nf:"fun (x::*) → fun (y:: * => *) → y x" ;

   (let f =
     "λ(x :: \
       < type fst::⋆ \
         type snd:: \
           < type fst::⋆ \
             type snd:: \
               (<type fst::⋆ type snd::⋆> ⇒ <type fst::⋆ type snd::⋆>) >>) \
     → x"
   and g =
    "λ(x :: \
       <type fst::⋆ \
        type snd:: \
          <type fst::⋆ \
           type snd:: \
             (<type fst::⋆ type snd::⋆> ⇒ <type fst::⋆ type snd::⋆>)>>) → \
  < type fst= x.fst \
    type snd= \
          < type fst = x.snd.fst \
            type snd = \
              λ(y :: <type fst::⋆ type snd::⋆>) → \
              < type fst = (x.snd.snd (<type fst=y.fst type snd=y.snd>)).fst \
                type snd = (x.snd.snd (<type fst=y.fst type snd=y.snd>)).snd > \
          > \
  >"
   in
   ("nf of " ^ f) >:: test_nf ~t:f ~nf:g) ;

   test_equiv
     ~neg:true
     ~env:(Env.empty)
     ~t:"λ (c :: *) → λ (x :: *) → c"
     ~u:"λ (c :: *) → λ (x :: *) → x"
     ~k:"* => * => *" () ;

   test_equiv
     ~env:(Env.empty)
     ~t:"λ (c :: *) → λ (x :: *) → c"
     ~u:"λ (c :: *) → λ (x :: *) → x"
     ~k:"Π(c :: *) => S(c) => *" () ;

   (let env =
     Env.Typ.add_var (Ast.Typ.Var.make "f") (String.Kind.parse "(* => *) => *")
       (Env.Typ.add_var (Ast.Typ.Var.make "c")
          (String.Kind.parse "*") Env.empty) in
   test_equiv
     ~neg:true
     ~env
     ~t:"f (λ (x :: *) → c)"
     ~u:"f (λ (x :: *) → x)"
     ~k:"*" ()) ;

   (let env =
     Env.Typ.add_var (Ast.Typ.Var.make "f")
       (String.Kind.parse "(S(c) => *) => *")
       (Env.Typ.add_var (Ast.Typ.Var.make "c")
          (String.Kind.parse "*") Env.empty) in
   test_equiv
     ~env
     ~t:"f (λ (x :: *) → c)"
     ~u:"f (λ (x :: *) → x)"
     ~k:"*" ()) ;
 ]

(* tests about wfterm *)
let test_wfterm ~e ~t =
  (Printf.sprintf "⊢ %s : %s?" e t) >:: (fun () ->
    let e = String.Term.parse e
    and t = String.Typ.parse t in
    assert_equal
      ~printer:PPrint.Typ.string
      ~cmp:(sub_type_b Env.empty) (Wfterm.wfterm Env.empty e) t)

let tests_wfterm = "Tests about wfterm" >:::
  [
   test_wfterm ~e:"fun (α:: *) (x : α) → x"
     ~t:"∀ (a:: *) a -> a" ;

   test_wfterm ~e:"fun (α:: *) (x : { val A: α val B: α }) → x"
     ~t:"∀ (a:: *) { val A:a val B: a } -> { val A: a val B: a }" ;

   test_wfterm
     ~e:"fun (α:: * => *) (β :: *) (x : { val A: α β  val B: α β }) → x"
     ~t:"∀ (α:: *=>*) ∀ (β::*) { val A: α β val B: α β } -> { val A: α β  val B: α β }" ;
 ]

(* tests about wfsubtype *)
let test_wfsubtype ~t ~u =
  (Printf.sprintf "⊢ %s ≤ %s?" t u) >:: (fun () ->
    let t = String.Typ.parse t
    and u = String.Typ.parse u in
    assert_equal
      ~printer:PPrint.Typ.string
      ~cmp:(sub_type_b Env.empty) t u)

let tests_wfsubtype = "Tests about wfsubtype" >:::
  [
   test_wfsubtype
     ~t:"∀ (a:: *) a -> a"
     ~u:"∀ (a:: *) a -> a" ;

   test_wfsubtype
     ~t:"∀ (a:: *) a -> a"
     ~u:"∀ (a:: S (forall (b::*) b)) a -> a" ;

   test_wfsubtype
     ~t:"∀ (a:: *) a -> a"
     ~u:"∀ (a:: S (forall (b::*) b)) (forall (b::*) b) -> a" ;

   test_wfsubtype
     ~t:"∀ (a:: *) (forall (b::*) b) -> a"
     ~u:"∀ (a:: S (forall (b::*) b)) a -> a" ;

   test_wfsubtype
     ~t:"∀ (a:: *) {val A:a val B:a} -> {val A:a val B:a}"
     ~u:"∀ (a:: *) {val B:a val A:a} -> {val B:a}" ;

   test_wfsubtype
     ~t:"∃ (a:: *) a -> a"
     ~u:"∃ (a:: *) a -> a" ;

   test_wfsubtype
     ~t:"∃ (a:: S (forall (b::*) b)) a -> a"
     ~u:"∃ (a:: *) a -> a" ;

   test_wfsubtype
     ~t:"∃ (a:: S (forall (b::*) b)) (forall (b::*) b) -> a"
     ~u:"∃ (a:: *) a -> a" ;

   test_wfsubtype
     ~t:"∃ (a:: S (forall (b::*) b)) a -> a"
     ~u:"∃ (a:: *) (forall (b::*) b) -> a" ;

   test_wfsubtype
     ~t:"∃ (a:: *) {val B:a val A:a} -> {val A:a val B:a}"
     ~u:"∃ (a:: *) {val A:a val B:a} -> {val B:a}" ;
 ]

(* tests about sub_kind *)
let test_sub_kind ~k1 ~k2 =
  (Printf.sprintf "⊢ %s ≤ %s?" k1 k2) >:: (fun () ->
    let k1 = String.Kind.parse k1
    and k2 = String.Kind.parse k2 in
    assert_equal
      ~printer:PPrint.Kind.string
      ~cmp:(sub_kind_b Env.empty) k1 k2)

let tests_sub_kind = "Tests about sub_kind" >:::
  [
   test_sub_kind
     ~k1:"Π (a:: *) => S(a)"
     ~k2:"Π (a:: *) => *" ;

   test_sub_kind
     ~k1:"Π (a:: *) (b :: *) => *"
     ~k2:"Π (a:: *) (b :: S(a)) => *" ;

   test_sub_kind
     ~k1:"Π (a:: *) (b :: S(a)) => S(a)"
     ~k2:"Π (a:: *) (b :: S(a)) => S(b)" ;

   test_sub_kind
     ~k1:"Π (a:: *) (b :: *) => S(a)"
     ~k2:"Π (a:: *) (b :: S(a)) => S(a)" ;

   test_sub_kind
     ~k1:"Π (a:: *) (b :: *) => S(a)"
     ~k2:"Π (a:: *) (b :: S(a)) => S(b)" ;

   test_sub_kind
     ~k1:"Π (a:: *) (b :: *) => S(a)"
     ~k2:"Π (a:: *) (b :: S({ val lab : a })) => S(a)" ;

   test_sub_kind
     ~k1:"< type left :: * type right :: * >"
     ~k2:"< >" ;

   test_sub_kind
     ~k1:"< type left :: * type right :: * >"
     ~k2:"< type left :: * >" ;

   test_sub_kind
     ~k1:"< type left :: * type right :: * >"
     ~k2:"< type right :: * >" ;

   test_sub_kind
     ~k1:"< type left :: * type right :: * >"
     ~k2:"< type right :: * type left :: * >" ;

   test_sub_kind
     ~k1:"< type left as α :: * type right :: S(α) >"
     ~k2:"< type right as β :: * type left :: S(β) >" ;

   test_sub_kind
     ~k1:"< type other as α :: * type left :: S(α) type right :: S(α) >"
     ~k2:"< type other :: * type right as β :: * type left :: S(β) >" ;

   test_sub_kind
     ~k1:"< type other as α :: * type left :: S(α) type right :: S(α) >"
     ~k2:"< type other as α :: * type right as β :: S(α) type left :: S(β) >" ;

   test_sub_kind
     ~k1:"< type other as α :: * type left :: S(α) type right :: S(α) >"
     ~k2:"< type other as α :: * type left as β :: S(α) type right :: S(β) >" ;

   test_sub_kind
     ~k1:"< type other as α :: * type left as β :: S(α) type right :: S(β) >"
     ~k2:"< type other as α :: * type left :: S(α) type right :: S(α) >" ;

   test_sub_kind
     ~k1:"< type other as α :: * type left :: S(α) type right :: S(α) >"
     ~k2:"< type right as α :: * type other as β :: S(α) type left :: S(β) >" ;

   test_sub_kind
     ~k1:"< type other as α :: * type left :: S(α) type right :: S(α) >"
     ~k2:"< type right as α :: * type other as β :: S(α) type left :: * >" ;

   test_sub_kind
     ~k1:"< type other as α :: * type left :: S(α) type right :: S(α) >"
     ~k2:"< type right as α :: * type left :: S(α) >" ;

   test_sub_kind
     ~k1:"< type deeper ::\
             < type other as α :: * type left :: S(α) type right :: S(α) > >"
     ~k2:"< type deeper :: < type right as α :: * type left :: S(α) > >" ;

   test_sub_kind
     ~k1:"< type left as α :: * \
            type right :: < type innerL :: S(α) type innerR :: * > >"
     ~k2:"< type right as β :: < type innerR :: * type innerL :: * > \
            type left :: S(β.innerL) >" ;

   test_sub_kind
     ~k1:"< type right as β :: < type innerR :: * type innerL :: * > \
            type left :: S(β.innerL) >"
     ~k2:"< type left as α :: * \
            type right :: < type innerL :: S(α) type innerR :: * > >" ;

   test_sub_kind
     ~k1:"< type A as a :: \
              < type C :: * type D :: * > \
            type B :: \
              < type E :: S(a.C) type F :: * > \
          >"
     ~k2:"< type B as b :: \
              < type F :: * type E :: * > \
            type A :: \
              < type D :: * type C :: S(b.E) > \
          >" ;

   test_sub_kind
     ~k1:"S(fun(x::*) → x :: Π(x::*) => S(x))"
     ~k2:"*=>*" ;

   test_sub_kind
     ~k1:"S(fun(x::*) → x :: Π(x::*) => S(x))"
     ~k2:"Π(x::*) => S(x)" ;

   test_sub_kind
     ~k1:"Π(x::*) => S(x)"
     ~k2:"S(fun(x::*) → x :: Π(x::*) => S(x))" ;

   test_sub_kind
     ~k1:"S(fun(x::*) → x :: Π(x::*) => S(x))"
     ~k2:"S(fun(x::*) → x :: Π(x::*) => S(x))" ;

   test_sub_kind
     ~k1:"S(fun(x::*) → x :: Π(x::*) => S(x))"
     ~k2:"S(fun(x::*) → x :: Π(x::*) => S(x))" ;

   test_sub_kind
     ~k1:"S(fun(x::*) → x :: Π(x::*) => S(x))"
     ~k2:"S(fun(x::*) → x :: *=>*)" ;

   test_sub_kind
     ~k1:"S(fun(x::*) → x :: *=>*)"
     ~k2:"S(fun(x::*) → x :: Π(x::*) => S(x))" ;

 ]

(* tests about equiv_typ *)
let test_equiv_typ ~t1 ~t2 ~k =
  (Printf.sprintf "⊢ %s ≡ %s :: %s ?" t1 t2 k) >:: (fun () ->
    let t1 = String.Typ.parse t1
    and t2 = String.Typ.parse t2
    and k = String.Kind.parse k in
    assert_equal
      ~printer:PPrint.Typ.string
      ~cmp:(fun t1 t2 -> Normalize.equiv_typ_b Env.empty t1 t2 k) t1 t2)

let tests_equiv_typ = "Tests about equiv_typ" >:::
  [
   test_equiv_typ
     ~t1:"∃ (α :: S (∀(β :: *) ∀(γ :: Π(δ::*) => S(δ)) γ β)) α"
     ~t2:"∃ (α :: S (∀(β :: *) ∀(γ :: Π(δ::*) => S(δ)) β)) α"
     ~k:"*" ;

   test_equiv_typ
     ~t1:"< type l = ∀(α::*)α  type q = ∀(α::*)∀(α::*)α >"
     ~t2:"< type r = ∀(α::*)∀(α::*)α  type l = ∀(α::*)α >"
     ~k:"< type l :: * >" ;

   test_equiv_typ
     ~t1:"< type l = ∀(α::*)α >"
     ~t2:"< type r = ∀(α::*)∀(α::*)α >"
     ~k:"< >" ;

 ]


(* all tests *)
let tests = TestList
    [ tests_parsing ; tests_wftype ; tests_nf ; tests_wfterm
    ; tests_wfsubtype ; tests_sub_kind ; tests_equiv_typ ]

(* running tests *)
let () =
  ignore (run_test_tt tests)
