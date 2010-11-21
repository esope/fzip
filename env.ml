open Mode

type typ_var = Ast.Typ.Var.free
type term_var = Ast.Term.Var.free

exception Removed_var of unit Location.located

type t =
    { term_vars: (term_var * Ast.Typ.t) list ;
      removed_term_vars: (unit Location.located) Ast.Term.Var.Map.t ;
      typ_vars: (typ_var * (mode Location.located * Ast.Kind.t)) list ;
      removed_typ_vars: (unit Location.located) Ast.Typ.Var.Map.t }

let empty =
  { term_vars = [] ; typ_vars = [] ;
    removed_term_vars = Ast.Term.Var.Map.empty ;
    removed_typ_vars  = Ast.Typ.Var.Map.empty  }

let clean_removed_vars { term_vars ; typ_vars ; _ } =
  { term_vars ; typ_vars ;
    removed_term_vars = Ast.Term.Var.Map.empty ;
    removed_typ_vars  = Ast.Typ.Var.Map.empty  }

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

let rec term_vars_to_string = function
  | [] -> ""
  | (x, t) :: e ->
      Printf.sprintf "val %s : %s\n%a"
        (Ast.Term.Var.to_string x)
        (Ast_utils.PPrint.Typ.string t)
        (fun _ -> term_vars_to_string) e

let rec typ_vars_to_string = function
  | [] -> ""
  | (x, ({ Location.content = Mode.U ; _ }, k)) :: e ->
      Printf.sprintf "∀ type %s :: %s\n%a"
        (Ast.Typ.Var.to_string x)
        (Ast_utils.PPrint.Kind.string k)
        (fun _ -> typ_vars_to_string) e
  | (x, ({ Location.content = Mode.E ; _ }, k)) :: e ->
      Printf.sprintf "∃ type %s :: %s\n%a"
        (Ast.Typ.Var.to_string x)
        (Ast_utils.PPrint.Kind.string k)
        (fun _ -> typ_vars_to_string) e
  | (x, ({ Location.content = Mode.EQ t ; _ }, k)) :: e ->
      Printf.sprintf "∀ type %s :: %s = %s\n%a"
        (Ast.Typ.Var.to_string x)
        (Ast_utils.PPrint.Kind.string k)
        (Ast_utils.PPrint.Typ.string t)
        (fun _ -> typ_vars_to_string) e


let to_string e =
  Printf.sprintf "begin\n%a%aend\n"
    (fun _ -> typ_vars_to_string)  (List.rev e.typ_vars)
    (fun _ -> term_vars_to_string) (List.rev e.term_vars)

module Set = struct
(* some operations on sets as records *)
  type ('elt, 'a) t =
      { empty: 'a ;
        is_empty: 'a -> bool ;
        singleton: 'elt -> 'a ;
        add: 'elt -> 'a -> 'a ;
        remove: 'elt -> 'a -> 'a ;
        inter: 'a -> 'a -> 'a ;
        union: 'a -> 'a -> 'a ;
        diff: 'a -> 'a -> 'a ;
        mem: 'elt -> 'a -> bool ;
        choose: 'a -> 'elt }

  let tyvar =
    let open Ast.Typ.Var.Set in
    { empty ; is_empty ; singleton ;
      add ; remove ; inter ; union ; diff ; mem ; choose }

  let tevar =
    let open Ast.Term.Var.Set in
    { empty ; is_empty ; singleton ;
      add ; remove ; inter ; union ; diff ; mem ; choose }
end

module Map = struct
(* some operations on maps as records *)
  type ('key, 'elem, 'a) mini_map =
      { empty: 'a ;
        is_empty: 'a -> bool ;
        mem: 'key -> 'a -> bool ;
        add: 'key -> 'elem -> 'a -> 'a ;
        equal: ('elem -> 'elem -> bool) -> 'a -> 'a -> bool ;
        merge: ('key -> 'elem option -> 'elem option -> 'elem option) ->
            'a -> 'a -> 'a ;
        partition: ('key -> 'elem -> bool) -> 'a -> 'a * 'a ;
        find: 'key -> 'a -> 'elem
      }

  let tyvar =
    let open Ast.Typ.Var.Map in
    { empty ; is_empty ; mem ; add ; equal ; merge ; partition ; find }
  let tevar =
    let open Ast.Term.Var.Map in
    { empty ; is_empty ; mem ; add ; equal ; merge ; partition ; find }
end

(* operations on association lists *)
let rec mem_assoc equal x = function
  | [] -> false
  | (y, _) :: l -> equal x y || mem_assoc equal x l

let rec get_assoc equal x = function
  | [] -> raise Not_found
  | (y, v) :: _ when equal x y -> v
  | _ :: l -> get_assoc equal x l

let rec remove_assoc equal x = function
  | [] -> []
  | (y, _) :: l when equal x y -> l
  | b :: l -> b :: remove_assoc equal x l

let rec remove_many_assocs mini_set vars = function
  | [] -> []
  | (y, _) :: l when mini_set.Set.mem y vars ->
      remove_many_assocs mini_set vars l
  | b :: l -> b :: remove_many_assocs mini_set vars l

let rec remove_many_assocs_map mini_set vars = function
  | [] -> []
  | (y, _) :: l when mini_set.Map.mem y vars ->
      remove_many_assocs_map mini_set vars l
  | b :: l -> b :: remove_many_assocs_map mini_set vars l

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
  else Answer.No (report_error different m2)

(* zipping the part with term variables *)
let te_zip e1 e2 =
  let (e31, _e1', e32, e2') = split_on_inter Set.tevar e1 e2 in
  let report_error m m' =
    let (x, t) = Ast.Term.Var.Map.choose m in
    let t' = try Ast.Term.Var.Map.find x m'
        with Not_found -> assert false in
    [ Answer.TERM_VAR_DISAGREE_TYP (t, t', x) ] in
  (* environment must agree on the intersection of their domains *)
  match equal_assoc_lists Map.tevar report_error Ast.Typ.equal e31 e32 with
  | Answer.Yes -> Answer.WithValue.Yes (e2' @ e1)
  | Answer.No reasons -> Answer.WithValue.No reasons

(* zipping the part with term variables *)
let ty_zip e1 e2 =
  let (e31, _e1', e32, e2') = split_on_inter Set.tyvar e1 e2 in
  let report_error m m' =
    let (a, (mode, k)) = Ast.Typ.Var.Map.choose m in
    let (mode', k') = try Ast.Typ.Var.Map.find a m'
    with Not_found -> assert false in
    if Ast.Kind.equal k k'
    then
      match (mode.Location.content, mode'.Location.content) with
      | (U, U) | (E, U) -> [] (* no error *)
      | (EQ ty, EQ ty') ->
          if Ast.Typ.equal ty ty'
          then [] (* no error *)
          else [ Answer.TYP_VAR_DISAGREE_EQEQ (mode, mode', a) ]
      | (E, E) -> (* duplication of linear items *)
          [ Answer.TYP_VAR_DISAGREE_EE (mode, mode', a) ]
      | (U, E) -> (* could lead to recursive types *)
          [ Answer.TYP_VAR_DISAGREE_UE (mode, mode', a) ]
      | (EQ _, U) -> (* inconsistent case *)
          [ Answer.TYP_VAR_DISAGREE_EQU (mode, mode', a) ]
      | (U, EQ _) -> (* inconsistent case *)
          [ Answer.TYP_VAR_DISAGREE_UEQ (mode, mode', a) ]
      | (EQ _, E) -> (* inconsistent case *)
          [ Answer.TYP_VAR_DISAGREE_EQE (mode, mode', a) ]
      | (E, EQ _) -> (* inconsistent case *)
          [ Answer.TYP_VAR_DISAGREE_EEQ (mode, mode', a) ]

    else
      [ Answer.TYP_VAR_DISAGREE_KIND
          (Location.locate_with k mode, Location.locate_with k' mode', a) ]
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
            let removed_term_vars = (* updating removed term variables *)
              let open Ast.Term.Var.Map in
              let rem1 =
                filter
                  (fun x _tau ->
                    not (mem_assoc Ast.Term.Var.equal x e1.term_vars))
                  e1.removed_term_vars
              and rem2 =
                filter
                  (fun x _tau ->
                    not (mem_assoc Ast.Term.Var.equal x e1.term_vars))
                  e2.removed_term_vars
              in
              merge
                (fun _ x y -> match x with | Some _ -> x | None -> y)
                rem1 rem2
            and removed_typ_vars = (* updating the removed type variables *)
              let open Ast.Typ.Var.Map in
              let rem1 =
                filter
                  (fun x _tau ->
                    not (mem_assoc Ast.Typ.Var.equal x e2.typ_vars))
                  e1.removed_typ_vars
              and rem2 =
                filter
                  (fun x _tau ->
                    not (mem_assoc Ast.Typ.Var.equal x e1.typ_vars))
                  e2.removed_typ_vars
              in
              merge
                (fun _ x y -> match x with | Some _ -> x | None -> y)
                rem1 rem2
            in
            Yes { term_vars = e_te ; typ_vars = e_ty ;
                  removed_term_vars = removed_term_vars ;
                  removed_typ_vars  = removed_typ_vars  }
        | (No _) as no -> no
      end
  | (No _) as no -> no

let filter p_te p_ty e =
  { term_vars = List.filter (fun (x, _) -> p_te x) e.term_vars ;
    removed_term_vars =
      Ast.Term.Var.Map.filter (fun x _ -> p_te x) e.removed_term_vars ;
    typ_vars = List.filter (fun (x, _) -> p_ty x) e.typ_vars ;
    removed_typ_vars =
      Ast.Typ.Var.Map.filter (fun x _ -> p_ty x) e.removed_typ_vars }

let free_vars mini_map fv e =
  List.fold_left
    (fun acc (x, t) -> mini_map.Map.add x (fv t) acc)
    mini_map.Map.empty e

(* Fixpoint of an increasing function, à la Tarski. *)
(* [fixpoint leq bottom f] computes the least fixpoint of [f] that is
   greater than [bottom], according to the ordering [leq]. *)
let fixpoint leq bottom f =
  let rec fix previous =
    let next = f previous in
    if leq next previous
    then previous
    else fix next
  in fix bottom

module Term = struct

  type var = term_var

  let get_var x e =
    try get_assoc Ast.Term.Var.equal x e.term_vars
    with Not_found ->
      let loc = Ast.Term.Var.Map.find x e.removed_term_vars in
      raise (Removed_var loc)

  let mem_var x e =
    try
      let _ = get_assoc Ast.Term.Var.equal x e.term_vars in
      true
    with Not_found -> false

  let add_var x t e =
    assert (not (mem_var x e)) ;
    { e with term_vars = (x, t) :: e.term_vars ;
      removed_term_vars = Ast.Term.Var.Map.remove x e.removed_term_vars }

  let remove_var ~track x loc e =
    { e with term_vars = remove_assoc Ast.Term.Var.equal x e.term_vars ;
      removed_term_vars =
      if track
      then Ast.Term.Var.Map.add x loc e.removed_term_vars
      else e.removed_term_vars }

end

module Typ = struct

  type var = typ_var
  type mode = Mode.mode

  let get_var x e =
    try get_assoc Ast.Typ.Var.equal x e.typ_vars
    with Not_found ->
      let loc = Ast.Typ.Var.Map.find x e.removed_typ_vars in
      raise (Removed_var loc)

  let mem_var x e =
    try
      let _ = get_assoc Ast.Typ.Var.equal x e.typ_vars in
      true
    with Not_found -> false

  let add_var mode x k e =
    assert (not (mem_var x e)) ;
    { e with typ_vars = (x, (mode, k)) :: e.typ_vars ;
      removed_typ_vars = Ast.Typ.Var.Map.remove x e.removed_typ_vars }

  let binding_fv ({ Location.content = mode ; _ }, k) =
    Ast.Typ.Var.Set.union
      (let open Mode in match mode with
      | U | E -> Ast.Typ.Var.Set.empty
      | EQ tau -> Ast.Typ.fv tau)
      (Ast.Kind.fv k)

  let locate_vars vars loc =
    Ast.Typ.Var.Set.fold
      (fun x acc -> Ast.Typ.Var.Map.add x loc acc)
      vars Ast.Typ.Var.Map.empty

  let vars_to_remove ~recursive x loc e =
    let (ty_vars_to_remove, te_vars_to_remove) =
      (* variables that come from the term variable environment *)
      if recursive
      then 
        List.fold_left
          (fun ((ty_vars, te_vars) as vars) (y, tau) ->
            let fv_tau = Ast.Typ.fv tau in
            if Ast.Typ.Var.Set.mem x fv_tau
            then (Ast.Typ.Var.Set.union fv_tau ty_vars,
                  Ast.Term.Var.Map.add y loc te_vars)
            else vars)
          (Ast.Typ.Var.Set.singleton x, Ast.Term.Var.Map.empty)
          e.term_vars
      else (Ast.Typ.Var.Set.singleton x, Ast.Term.Var.Map.empty)
    in
    let ty_vars_to_remove =
      (* variables that come from the type variable environment *)
      if recursive
      then
        let open Ast.Typ.Var.Set in
        fixpoint subset ty_vars_to_remove
          (fun vars ->
            union vars
              (List.fold_left
                 (fun acc (var, b) -> let fv = binding_fv b in
                 if is_empty (inter fv vars) then acc else add var acc)
                 empty e.typ_vars))
      else ty_vars_to_remove
    in
    assert (Ast.Typ.Var.Set.mem x ty_vars_to_remove) ;
    (locate_vars ty_vars_to_remove loc, te_vars_to_remove)

  let remove_var ~track ~recursive x (loc: unit Location.located) e =
    let (ty_vars_to_remove, te_vars_to_remove) =
      vars_to_remove ~recursive x loc e in
    { term_vars =
        remove_many_assocs_map Map.tevar te_vars_to_remove e.term_vars ;
      removed_term_vars =
        if track
        then
          Ast.Term.Var.Map.merge
            (fun _key x y -> match (x, y) with
            | (Some x, _) -> Some x
            | (_, _) -> y)
            e.removed_term_vars
            te_vars_to_remove
        else e.removed_term_vars ;
      typ_vars =
        remove_many_assocs_map Map.tyvar ty_vars_to_remove e.typ_vars ;
      removed_typ_vars =
        if track
        then
          Ast.Typ.Var.Map.merge
            (fun _key x y -> match (x, y) with
            | (Some x, _) -> Some x
            | (_, _) -> y)
            e.removed_typ_vars
            ty_vars_to_remove
        else e.removed_typ_vars 
    }

  let is_fv y e =
    List.exists (fun (_x, t) -> Ast.Typ.is_fv y t) e.term_vars ||
    List.exists
      (fun (_x, ({ Location.content = mode ; _ }, k)) ->
        Ast.Kind.is_fv y k ||
        (match mode with
        | Mode.EQ tau -> Ast.Typ.is_fv y tau
        | Mode.E | Mode.U -> false))
      e.typ_vars

  let exist_vars { typ_vars ; _ } =
    List.fold_left
      (fun acc (x, (mode, _k)) ->
        match mode.Location.content with
        | Mode.E -> Ast.Typ.Var.Map.add x mode acc
        | Mode.U | Mode.EQ _ -> acc)
      Ast.Typ.Var.Map.empty typ_vars

  let minimal_deps_in_env env vars =
    fixpoint Ast.Typ.Var.Set.subset vars
      (fun vars ->
          Ast.Typ.Var.Set.fold
          (fun x acc ->
            Ast.Typ.Var.Set.union (binding_fv (get_var x env)) acc)
          vars vars)

  let minimal_env_for_vars env vars =
    filter
      (fun _ -> false)
      (fun x -> Ast.Typ.Var.Set.mem x (minimal_deps_in_env env vars))
      env

end
