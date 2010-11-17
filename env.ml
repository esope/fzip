open Mode

type typ_var = Ast.Typ.Var.free
type term_var = Ast.Term.Var.free

type t =
    { term_vars: (term_var * Ast.Typ.t) list ;
      typ_vars: (typ_var * (mode Location.located * Ast.Kind.t)) list }

let empty = { term_vars = [] ; typ_vars = [] }

let is_pure { typ_vars ; _ } =
  let open Answer in
  try
    let (a, (loc, _)) =
      List.find
        (fun (_, ({ Location.content = mode ; _ }, _)) -> match mode with
        | E -> true
        | U | EQ _ -> false)
        typ_vars
    in No [ E_TYP_VAR_PURE (Location.locate_with a loc) ]
  with Not_found -> Yes

module Set = struct
(* some operations on sets as records *)
  type ('elt, 'a) t =
      { empty: 'a ; add: 'elt -> 'a -> 'a ;
        inter: 'a -> 'a -> 'a ; mem: 'elt -> 'a -> bool }

  let tyvar =
    let open Ast.Typ.Var.Set in
    { empty ; add ; inter ; mem }

  let tevar =
    let open Ast.Term.Var.Set in
    { empty ; add ; inter ; mem }
end

module Map = struct
(* some operations on maps as records *)
  type ('key, 'elem, 'a) mini_map =
      { empty: 'a ; add: 'key -> 'elem -> 'a -> 'a ;
        is_empty: 'a -> bool ;
        equal: ('elem -> 'elem -> bool) -> 'a -> 'a -> bool ;
        merge: ('key -> 'elem option -> 'elem option -> 'elem option) ->
            'a -> 'a -> 'a ;
        partition: ('key -> 'elem -> bool) -> 'a -> 'a * 'a ;
        find: 'key -> 'a -> 'elem
      }

  let tyvar =
    let open Ast.Typ.Var.Map in
    { empty ; is_empty ; add ; equal ; merge ; partition ; find }
  let tevar =
    let open Ast.Term.Var.Map in
    { empty ; is_empty ; add ; equal ; merge ; partition ; find }
end

let dom mini_set e =
  List.fold_left (fun dom (a, _) -> mini_set.Set.add a dom)
    mini_set.Set.empty e

(* when [l1] and [l2] are association lists, [split_on_inter l1 l2]
   returns [(l31, l1', l32, l2')], where:
   - [l31] is [l1] restricted to [dom l1 ∩ dom l2]
   - [l32] is [l2] restricted to [dom l1 ∩ dom l2]
   - [l1'] is such that [l1 = l31 ∪ l1']
   - [l2'] is such that [l2 = l32 ∪ l2']
 *)
let split_on_inter mini_set l1 l2 =
  let dom_inter = mini_set.Set.inter (dom mini_set l1) (dom mini_set l2) in
  let (l31, l1') =
    List.partition (fun (a, _) -> mini_set.Set.mem a dom_inter) l1
  and (l32, l2') =
    List.partition (fun (a, _) -> mini_set.Set.mem a dom_inter) l2 in
  (l31, l1', l32, l2')

let equal_assoc_lists mini_map report_error equal l1 l2 =
  let m1 = List.fold_left
      (fun acc (a, x) -> mini_map.Map.add a x acc) mini_map.Map.empty l1
  and m2 = List.fold_left
      (fun acc (a,x) -> mini_map.Map.add a x acc) mini_map.Map.empty l2 in
  let (_identical, different) = mini_map.Map.partition
      (fun k x -> equal x (mini_map.Map.find k m2)) m1 in
  if mini_map.Map.is_empty different
  then Answer.Yes
  else Answer.No (report_error different)
      (* should output the two different items -> needs m2 *)

(* zipping the part with term variables *)
let te_zip e1 e2 =
  let (e31, _e1', e32, e2') = split_on_inter Set.tevar e1 e2 in
  let report_error m =
    let (x, t) = Ast.Term.Var.Map.choose m in
    [ Answer.TERM_VAR_DISAGREE (Location.locate_with x t) ] in
  (* environment must agree on the intersection of their domains *)
  match equal_assoc_lists Map.tevar report_error Ast.Typ.equal e31 e32 with
  | Answer.Yes -> Answer.WithValue.Yes (e2' @ e1)
  | Answer.No reasons -> Answer.WithValue.No reasons

(* zipping the part with term variables *)
let ty_zip e1 e2 =
  let (e31, _e1', e32, e2') = split_on_inter Set.tyvar e1 e2 in
  let report_error m =
    let (a, (mode, _k)) = Ast.Typ.Var.Map.choose m in
    [ Answer.TYP_VAR_DISAGREE (mode, a) ]
  and authorized_bindings
      ({ Location.content = mode1 ; _ }, k1)
      ({ Location.content = mode2 ; _ }, k2) =
    Ast.Kind.equal k1 k2 &&
    begin
      match (mode1, mode2) with
      | (U, U) | (E, U) -> true
      | (EQ ty1, EQ ty2) -> Ast.Typ.equal ty1 ty2
      | (E, E) -> false (* duplication of linear items *)
      | (U, E) -> false (* could lead to recursive types *)
      | ((U | E | EQ _), _) -> false (* inconsistent cases *)
    end in
  (* environment must agree on the intersection of their domains *)
  match equal_assoc_lists Map.tyvar report_error authorized_bindings e31 e32
  with
  | Answer.Yes -> Answer.WithValue.Yes (e2' @ e1)
  | Answer.No reasons -> Answer.WithValue.No reasons

let zip e1 e2 =
  let open Answer.WithValue in
  match te_zip e1.term_vars e2.term_vars with
  | Yes e_te ->
      begin
        match ty_zip e1.typ_vars e2.typ_vars with
        | Yes e_ty ->
            Yes { term_vars = e_te ; typ_vars = e_ty }
        | (No _) as no -> no
      end
  | (No _) as no -> no

let rec get_assoc equal x = function
  | [] -> raise Not_found
  | (y, v) :: _ when equal x y -> v
  | _ :: l -> get_assoc equal x l

let rec remove_assoc equal x = function
  | [] -> []
  | (y, _) :: l when equal x y -> l
  | b :: l -> b :: b :: remove_assoc equal x l

module Term = struct

  type var = term_var

  let get_var x e = get_assoc Ast.Term.Var.equal x e.term_vars

  let add_var x t e =
    { e with term_vars = (x, t) :: e.term_vars }

  let remove_var x e =
    { e with term_vars = remove_assoc Ast.Term.Var.equal x e.term_vars }

end

module Typ = struct

  type var = typ_var
  type mode = Mode.mode

  let get_var x e = get_assoc Ast.Typ.Var.equal x e.typ_vars

  let add_var mode x k e =
    { e with typ_vars = (x, (mode, k)) :: e.typ_vars }

(* TODO: remove dependencies as well *)
  let remove_var x e =
    { e with typ_vars = remove_assoc Ast.Typ.Var.equal x e.typ_vars }

  let is_fv y e =
    List.exists (fun (_x, t) -> Ast.Typ.is_fv y t) e.term_vars ||
    List.exists
      (fun (_x, ({ Location.content = mode ; _ }, k)) ->
        Ast.Kind.is_fv y k ||
        (match mode with
        | Mode.EQ tau -> Ast.Typ.is_fv y tau
        | Mode.E | Mode.U -> false))
      e.typ_vars
end
