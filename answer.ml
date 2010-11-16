open Ast
open Ast_utils

type reason =
  | TYPES of Typ.t * Typ.t
  | KINDS of Kind.t * Kind.t
  | WF_TYPE of Typ.t * Kind.t
  | E_TYP_VAR_PURE of Typ.Var.free Location.located
  | TERM_VAR_DISAGREE of Term.Var.free Location.located
  | TYP_VAR_DISAGREE of Mode.mode Location.located * Typ.Var.free
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
      Printf.sprintf "The type variable %s is an existential item that is not consumed.\nIt was introduced in file %s, at line %i, characters %i-%i.\n%!"
        (Typ.Var.to_string a)
        startpos.pos_fname
        startpos.pos_lnum
        (startpos.pos_cnum - startpos.pos_bol)
        (endpos.pos_cnum - startpos.pos_bol)
  | [ TERM_VAR_DISAGREE { Location.content = x ; startpos ; endpos }] ->
      let open Lexing in
      Printf.sprintf "The term variable %s is assigned two different types while zipping environments.\nIt was introduced in file %s, at line %i, characters %i-%i.\n%!"
        (Term.Var.to_string x)
        startpos.pos_fname
        startpos.pos_lnum
        (startpos.pos_cnum - startpos.pos_bol)
        (endpos.pos_cnum - startpos.pos_bol)
  | [ TYP_VAR_DISAGREE ({ Location.content = _mode ; startpos ; endpos }, x)] ->
      let open Lexing in
      Printf.sprintf "The type variable %s is assigned two different kinds or modes while zipping\nenvironments.\nIt was introduced in file %s, at line %i, characters %i-%i.\n%!"
        (Typ.Var.to_string x)
        startpos.pos_fname
        startpos.pos_lnum
        (startpos.pos_cnum - startpos.pos_bol)
        (endpos.pos_cnum - startpos.pos_bol)
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
  | (E_TYP_VAR_PURE _ | TERM_VAR_DISAGREE _ | TYP_VAR_DISAGREE _) :: _ ->
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
