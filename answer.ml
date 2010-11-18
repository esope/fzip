open Ast
open Ast_utils

type reason =
  | TYPES of Typ.t * Typ.t
  | KINDS of Kind.t * Kind.t
  | WF_TYPE of Typ.t * Kind.t
  | E_TYP_VAR_PURE of Typ.Var.free Location.located
  | TERM_VAR_DISAGREE_TYP of
      Typ.t * Typ.t * Term.Var.free
  | TYP_VAR_DISAGREE_KIND of
      Kind.t Location.located * Kind.t Location.located * Typ.Var.free
  | TYP_VAR_DISAGREE_EE of
      Mode.mode Location.located * Mode.mode Location.located * Typ.Var.free
  | TYP_VAR_DISAGREE_UE of
      Mode.mode Location.located * Mode.mode Location.located * Typ.Var.free
  | TYP_VAR_DISAGREE_EEQ of
      Mode.mode Location.located * Mode.mode Location.located * Typ.Var.free
  | TYP_VAR_DISAGREE_EQE of
      Mode.mode Location.located * Mode.mode Location.located * Typ.Var.free
  | TYP_VAR_DISAGREE_UEQ of
      Mode.mode Location.located * Mode.mode Location.located * Typ.Var.free
  | TYP_VAR_DISAGREE_EQU of
      Mode.mode Location.located * Mode.mode Location.located * Typ.Var.free
  | TYP_VAR_DISAGREE_EQEQ of
      Mode.mode Location.located * Mode.mode Location.located * Typ.Var.free

type t = Yes | No of reason list

let ( &*& ) r1 r2 = match r1 with
| Yes -> r2
| No _ -> r1

let from_bool b = if b then Yes else No []
let to_bool = function Yes -> true | No _ -> false

let rec error_msg = function
  | [] -> assert false
  | [ KINDS (k1, k2)] ->
      Printf.sprintf "%s\nis not a subkind of\n%s\n%!"
        (PPrint.Kind.string k1) (PPrint.Kind.string k2)
  | [ TYPES (t1, t2)] ->
      Printf.sprintf "%s\nis not a subtype of\n%s\n%!"
        (PPrint.Typ.string t1) (PPrint.Typ.string t2)
  | [ WF_TYPE (t, k)] ->
      Printf.sprintf "%s\n cannot be given the kind\n%s\n%!"
        (PPrint.Typ.string t) (PPrint.Kind.string k)
  | [ E_TYP_VAR_PURE { Location.content = a ; startpos ; endpos }] ->
      let open Lexing in
      Printf.sprintf "The existential type variable %s is not closed nor restricted.\nIt was used in file %s, at line %i, characters %i-%i.\n%!"
        (Typ.Var.to_string a)
        startpos.pos_fname startpos.pos_lnum startpos.pos_cnum
        (endpos.pos_cnum + (endpos.pos_bol - startpos.pos_bol))
  | [ TERM_VAR_DISAGREE_TYP
        (({ Location.startpos = start1 ; endpos = end1 ; _ } as t1),
         ({ Location.startpos = start2 ; endpos = end2 ; _ } as t2),
         x) ] ->
      let open Lexing in
      Printf.sprintf "The term variable %s is assigned two different types while zipping environments.\nIn file %s, at line %i, characters %i-%i, it has type\n%s\nwhereas in file %s, at line %i, characters %i-%i, it has type\n%s\n%!"
        (Term.Var.to_string x)
        start1.pos_fname start1.pos_lnum start1.pos_cnum
        (end1.pos_cnum + (end1.pos_bol - start1.pos_bol))
        (Ast_utils.PPrint.Typ.string t1)
        start2.pos_fname start2.pos_lnum start2.pos_cnum
        (end2.pos_cnum + (end2.pos_bol - start2.pos_bol))
        (Ast_utils.PPrint.Typ.string t2)
  | [ TYP_VAR_DISAGREE_KIND
        ({ Location.content = k1 ; startpos = start1 ; endpos = end1 },
         { Location.content = k2 ; startpos = start2 ; endpos = end2 },
         x) ] ->
      let open Lexing in
      Printf.sprintf "The type variable %s is assigned two different kinds while zipping environments.\nIn file %s, at line %i, characters %i-%i, it has kind\n%s\nwhereas in file %s, at line %i, characters %i-%i, it has kind\n%s\n%!"
        (Typ.Var.to_string x)
        start1.pos_fname start1.pos_lnum start1.pos_cnum
        (end1.pos_cnum + (end1.pos_bol - start1.pos_bol))
        (Ast_utils.PPrint.Kind.string k1)
        start2.pos_fname start2.pos_lnum start2.pos_cnum
        (end2.pos_cnum + (end2.pos_bol - start2.pos_bol))
        (Ast_utils.PPrint.Kind.string k2)
  | [ TYP_VAR_DISAGREE_EE
        ({ Location.content = _ ; startpos = start1 ; endpos = end1 },
         { Location.content = _ ; startpos = start2 ; endpos = end2 },
         x) ] ->
      let open Lexing in
      Printf.sprintf "The type variable %s is used twice to create existential types in file %s, at line %i, characters %i-%i, and in file %s, at line %i, characters %i-%i.\n%!"
        (Typ.Var.to_string x)
        start1.pos_fname start1.pos_lnum start1.pos_cnum
        (end1.pos_cnum + (end1.pos_bol - start1.pos_bol))
        start2.pos_fname start2.pos_lnum start2.pos_cnum
        (end2.pos_cnum + (end2.pos_bol - start2.pos_bol))
  | [ TYP_VAR_DISAGREE_UE
        ({ Location.content = _ ; startpos = start1 ; endpos = end1 },
         { Location.content = _ ; startpos = start2 ; endpos = end2 },
         x) ] ->
      let open Lexing in
      Printf.sprintf "The existential type variable %s is used before its witness has been defined. It is used in file %s, at line %i, characters %i-%i, and defined later in file %s, at line %i, characters %i-%i.\n%!"
        (Typ.Var.to_string x)
        start1.pos_fname start1.pos_lnum start1.pos_cnum
        (end1.pos_cnum + (end1.pos_bol - start1.pos_bol))
        start2.pos_fname start2.pos_lnum start2.pos_cnum
        (end2.pos_cnum + (end2.pos_bol - start2.pos_bol))
  | [ TYP_VAR_DISAGREE_EQEQ
        ({ Location.content = mode1 ; startpos = start1 ; endpos = end1 },
         { Location.content = mode2 ; startpos = start2 ; endpos = end2 },
         x) ] ->
           begin
             match (mode1, mode2) with
             | (Mode.EQ t1, Mode.EQ t2) ->
                 let open Lexing in
                 Printf.sprintf "The type variable %s is assigned two different equations while zipping environments.\nIn file %s, at line %i, characters %i-%i, it is said to be equal to the type\n%s\nwhereas in file %s, at line %i, characters %i-%i, it is said to be equal to the type\n%s\n%!"
                   (Typ.Var.to_string x)
                   start1.pos_fname start1.pos_lnum start1.pos_cnum
                   (end1.pos_cnum + (end1.pos_bol - start1.pos_bol))
                   (Ast_utils.PPrint.Typ.string t1)
                   start2.pos_fname start2.pos_lnum start2.pos_cnum
                   (end2.pos_cnum + (end2.pos_bol - start2.pos_bol))
                   (Ast_utils.PPrint.Typ.string t2)
             | ((Mode.U | Mode.E | Mode.EQ _), _) -> assert false
           end
  | [ TYP_VAR_DISAGREE_EEQ
        ({ Location.content = _ ; startpos = start1 ; endpos = end1 },
         { Location.content = _ ; startpos = start2 ; endpos = end2 },
         x) ] ->
      let open Lexing in
      Printf.sprintf "The existential type variable %s is used to create an existential type in file %s, at line %i, characters %i-%i, whereas it holds an equation in file %s, at line %i, characters %i-%i.\n%!"
        (Typ.Var.to_string x)
        start1.pos_fname start1.pos_lnum start1.pos_cnum
        (end1.pos_cnum + (end1.pos_bol - start1.pos_bol))
        start2.pos_fname start2.pos_lnum start2.pos_cnum
        (end2.pos_cnum + (end2.pos_bol - start2.pos_bol))
  | [ TYP_VAR_DISAGREE_EQE
        ({ Location.content = _ ; startpos = start1 ; endpos = end1 },
         { Location.content = _ ; startpos = start2 ; endpos = end2 },
         x) ] ->
      let open Lexing in
      Printf.sprintf "The existential type variable %s holds an equation in file %s, at line %i, characters %i-%i, whereas it is used to create an existential type in file %s, at line %i, characters %i-%i.\n%!"
        (Typ.Var.to_string x)
        start1.pos_fname start1.pos_lnum start1.pos_cnum
        (end1.pos_cnum + (end1.pos_bol - start1.pos_bol))
        start2.pos_fname start2.pos_lnum start2.pos_cnum
        (end2.pos_cnum + (end2.pos_bol - start2.pos_bol))

  | [ TYP_VAR_DISAGREE_UEQ
        ({ Location.content = _ ; startpos = start1 ; endpos = end1 },
         { Location.content = _ ; startpos = start2 ; endpos = end2 },
         x) ] ->
      let open Lexing in
      Printf.sprintf "The type variable %s does not hold an equation in file %s, at line %i, characters %i-%i, whereas it holds an equation in file %s, at line %i, characters %i-%i.\n%!"
        (Typ.Var.to_string x)
        start1.pos_fname start1.pos_lnum start1.pos_cnum
        (end1.pos_cnum + (end1.pos_bol - start1.pos_bol))
        start2.pos_fname start2.pos_lnum start2.pos_cnum
        (end2.pos_cnum + (end2.pos_bol - start2.pos_bol))
  | [ TYP_VAR_DISAGREE_EQU
        ({ Location.content = _ ; startpos = start1 ; endpos = end1 },
         { Location.content = _ ; startpos = start2 ; endpos = end2 },
         x) ] ->
      let open Lexing in
      Printf.sprintf "The type variable %s holds an equation in file %s, at line %i, characters %i-%i, whereas it does not hold an equation in file %s, at line %i, characters %i-%i.\n%!"
        (Typ.Var.to_string x)
        start1.pos_fname start1.pos_lnum start1.pos_cnum
        (end1.pos_cnum + (end1.pos_bol - start1.pos_bol))
        start2.pos_fname start2.pos_lnum start2.pos_cnum
        (end2.pos_cnum + (end2.pos_bol - start2.pos_bol))

  | (KINDS (k1, k2)) :: l ->
      Printf.sprintf "%s\nis not a subkind of\n%s\nbecause\n%a"
        (PPrint.Kind.string k1) (PPrint.Kind.string k2)
        (fun _ -> error_msg) l
  | (TYPES (t1, t2)) :: l ->
      Printf.sprintf "%s\nis not a subtype of\n%s\nbecause\n%a"
        (PPrint.Typ.string t1) (PPrint.Typ.string t2)
        (fun _ -> error_msg) l
  | (WF_TYPE (t, k)) :: l ->
      Printf.sprintf "%s\n cannot be given the kind\n%s\nbecause\n%a"
        (PPrint.Typ.string t) (PPrint.Kind.string k)
        (fun _ -> error_msg) l
  | (E_TYP_VAR_PURE _ | TERM_VAR_DISAGREE_TYP _ |
    TYP_VAR_DISAGREE_KIND _ | TYP_VAR_DISAGREE_EQU _ |
    TYP_VAR_DISAGREE_UEQ _ | TYP_VAR_DISAGREE_EQE _ |
    TYP_VAR_DISAGREE_EEQ _ | TYP_VAR_DISAGREE_EQEQ _ |
    TYP_VAR_DISAGREE_UE _ | TYP_VAR_DISAGREE_EE _) :: _ ->
      assert false

module WithValue = struct

  type 'a t = Yes of 'a | No of reason list

  let ( &*& ) r1 r2 = match r1 with
  | Yes _ -> r2
  | No _ -> r1

  let to_bool = function Yes _ -> true | No _ -> false

  let map f = function
    | Yes x -> Yes (f x)
    | No r -> No r

  let error_msg = error_msg

end
