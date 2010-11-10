open Ast
open Ast_utils

type reason = TYPES of Typ.t * Typ.t | KINDS of Kind.t * Kind.t
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
  | (KINDS (k1, k2)) :: l ->
      Printf.sprintf "%s\nis not a subkind of\n%s\nbecause\n%a"
        (PPrint.Kind.string k1) (PPrint.Kind.string k2)
        (fun _ -> error_msg) l
  | (TYPES (t1, t2)) :: l ->
      Printf.sprintf "%s\nis not a subtype of\n%s\nbecause\n%a"
        (PPrint.Typ.string t1) (PPrint.Typ.string t2)
        (fun _ -> error_msg) l

module WithValue = struct

  type 'a t = Yes of 'a | No of reason list

  let ( &*& ) r1 r2 = match r1 with
  | Yes _ -> r2
  | No _ -> r1

  let to_bool = function Yes _ -> true | No _ -> false

  let error_msg = error_msg

end
