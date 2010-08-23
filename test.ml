open Ast
open Ast_utils
open Parse_utils

let run_bintests f1 f2 examples =
  let failed = ref 0 in
  let i = ref 0 in
  let () =
    List.iter (fun e ->
      incr i;
      Printf.printf "TEST #%i (n=%i, h=%i, bh=%i, b=%i): %!"
        (!i) (Measure.size e) (Measure.height e)
        (Measure.bheight e) (Measure.nb_binders e);
      let e1 = (Printf.printf "(1%!" ;
                let e1 = f1 e in Printf.printf ")%!" ; e1) in
      let e2 = (Printf.printf "(2%!" ;
                let e2 = f2 e in Printf.printf ")%! " ; e2) in
      if e1 = e2 then Printf.printf "PASSED\n%!" 
      else
        begin
          incr failed;
          Printf.printf
            "FAILED:\n  Input:   %a\n  Output1: %a\n  Output2: %a\n%!"
            (fun _ -> Print.typ) e
            (fun _ -> Print.typ) e1
            (fun _ -> Print.typ) e2
        end)
      examples in
  if !failed = 0 then
    Printf.printf "All tests passed.\n%!"
  else
    Printf.printf "%i test(s) failed.\n%!" (!failed)

let run_tests f test cases =
  let failed = ref 0 in
  let i = ref 0 in
  let () =
    List.iter (fun (q,e) ->
      incr i;
      Printf.printf "TEST #%i (n=%i, h=%i, bh=%i, b=%i): %!"
        (!i) (Measure.size q) (Measure.height q)
        (Measure.bheight q) (Measure.nb_binders q);
      let a = (Printf.printf "(1%!" ;
                let e1 = f q in Printf.printf ") %!" ; e1) in
      if test a e then Printf.printf "PASSED\n%!" 
      else
        begin
          incr failed;
          Printf.printf
            "FAILED:\n  Input:    %a\n  Output:   %a\n  Expected: %a\n%!"
            (fun _ -> Print.typ) q
            (fun _ -> Print.kind) a
            (fun _ -> Print.kind) e
        end)
      cases in
  if !failed = 0 then
    Printf.printf "All tests passed.\n%!"
  else
    Printf.printf "%i test(s) failed.\n%!" (!failed)

let rec init f = function
  | 0 -> []
  | n -> (f ()) :: init f (n-1)

module STLC = struct
  open Wftype

  let () = Printf.printf "-- Tests STLC\n%!"

  let () = run_tests (wftype []) (wfsub [])
      [ (String.parse_typ "fun (x::*) x",
         String.parse_kind "* => *") ;
        (String.parse_typ "fun (x::*) fun (y::*=>*) y x",
         String.parse_kind "* => (* => *) => *") ;
      ]

  open Normalize

  let nf e =
    let tau = wftype [] e in
    typ_norm [] e tau

  let print_nf e =
    Print.typ (nf e); print_newline ()

  let () =
    let s = "fun (x::*) fun (y::* => *) y x" in
    Printf.printf "--- NF of %s:\n%!" s ;
    let e = String.parse_typ s in
    print_nf e ;
    print_newline ()

  let mknum_string n =
    let rec mkapp_n t1 t2 = function
      | 0 -> Printf.sprintf "%s" t2
      | n -> Printf.sprintf "((%s) (%s))" t1 (mkapp_n t1 t2 (n-1))
    in
    Printf.sprintf "(λ(f :: ⋆ ⇒ ⋆) λ(x :: ⋆) %s)" (mkapp_n "f" "x" n)

  let mknum n = String.parse_typ (mknum_string n)

  let nat_string = "(* => *) => * => *"
  let nat = String.parse_kind nat_string

  let add_string = 
    ("(λ (n :: " ^ nat_string ^ ")" ^
     " λ (m :: " ^ nat_string ^ ")" ^
     " λ (f :: ⋆ ⇒ ⋆) λ (x :: ⋆) n f (m f x))")
  let add = String.parse_typ add_string

  let () =
    Printf.printf "--- NF of %s\n%!" add_string ;
    print_nf add ;
    print_newline () ;

    let s = add_string ^ (mknum_string 3) ^ (mknum_string 4) in
    Printf.printf "--- NF of %s\n%!" s ;
    print_nf (String.parse_typ s) ;
    print_newline () ;

    Printf.printf "--- 42 + 96 = 138? %b\n%!"
      (eq_typ
         (nf (String.parse_typ
                (add_string ^ (mknum_string 42) ^ (mknum_string 96))))
         (nf (String.parse_typ (mknum_string 138)))) ;
    print_newline () ;

    let s = "λ(x :: ⋆ × ⋆ × (⋆ × ⋆ ⇒ ⋆ × ⋆)) x" in
    Printf.printf "--- NF of %s:\n%!" s ;
    print_nf (String.parse_typ s) ;
    print_newline () ;

    let k = "* => * => *"
    and k' = "Π(c :: *) S(c) => *"
    and t1 = "λ (c :: *) λ (x :: *) c"
    and t2 = "λ (c :: *) λ (x :: *) x" in
    Printf.printf "⊢  %s\n≡  %s\n:: %s ?\n--> %b (false expected)\n%!"
      t1 t2 k
      (equiv_typ []
         (String.parse_typ t1) (String.parse_typ t2) (String.parse_kind k)) ;
    print_newline () ;
    Printf.printf "⊢  %s\n≡  %s\n:: %s ?\n--> %b (true expected)\n%!"
      t1 t2 k'
      (equiv_typ []
         (String.parse_typ t1) (String.parse_typ t2) (String.parse_kind k')) ;
    print_newline () ;

    let k = "(* => *) => *"
    and k' = "(S(c) => *) => *"
    and t1 = "f (λ (x :: *) x)"
    and t2 = "f (λ (x :: *) c)" in
    Printf.printf "c:: *, f:: %s\n⊢  %s\n≡  %s\n:: %s ?\n--> %b (false expected)\n%!"
      k t1 t2 "*"
      (equiv_typ [("c", Base); ("f", String.parse_kind k)]
         (String.parse_typ t1) (String.parse_typ t2) Base) ;
    print_newline () ;

    Printf.printf "c:: *, f:: %s\n⊢  %s\n≡  %s\n:: %s ?\n--> %b (true expected)\n%!"
      k' t1 t2 "*"
      (equiv_typ [("c", Base); ("f", String.parse_kind k')]
         (String.parse_typ t1) (String.parse_typ t2) Base) ;
    print_newline () ;

end
