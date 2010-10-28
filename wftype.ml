open Ast.Typ
open Ast_utils
open Location

module Sub_result = struct
  type 'a t = Yes | No of ('a * 'a) list

  let ( &*& ) r1 r2 = match r1 with
  | Yes -> r2
  | _ -> r1

  let from_bool b = if b then Yes else No []
  let to_bool = function Yes -> true | No _ -> false
end
open Sub_result

let rec subkind_error_msg = function
  | [] -> assert false
  | [(k1, k2)] ->
      Printf.sprintf "%s\nis not a subkind of\n%s\n%!"
        (PPrint.Kind.string k1) (PPrint.Kind.string k2)
  | (k1, k2) :: l ->
      Printf.sprintf "%s\nis not a subkind of\n%s\nbecause\n%a"
        (PPrint.Kind.string k1) (PPrint.Kind.string k2)
        (fun _ -> subkind_error_msg) l

let rec subtype_error_msg = function
  | [] -> assert false
  | [(t1, t2)] ->
      Printf.sprintf "%s\nis not a subtype of\n%s\n%!"
        (PPrint.Typ.string t1) (PPrint.Typ.string t2)
  | (t1, t2) :: l ->
      Printf.sprintf "%s\nis not a subtype of\n%s\nbecause\n%a"
        (PPrint.Typ.string t1) (PPrint.Typ.string t2)
        (fun _ -> subtype_error_msg) l

type env = (typ, typ kind) Env.t

let rec single_ext k t = match k with
| Base -> Single t
| Single u as k -> k
| Arrow(k1, k2) ->
    let x = new_var () in
    let x_var = dummy_locate (FVar x) in
    let k2' = single_ext k2 (dummy_locate (App(t, x_var))) in
    mkPi x k1 k2'
| Pi(y, k1, k2) ->
    let x = new_var () in
    let x_var = dummy_locate (FVar x) in
    let k2' =
      single_ext (bsubst_kind k2 y x_var) (dummy_locate (App(t, x_var))) in
    mkPi x k1 k2'
| Prod(k1, k2) ->
    let k1' = single_ext k1 (dummy_locate (Proj(t, "fst")))
    and k2' = single_ext k2 (dummy_locate (Proj(t, "snd"))) in
    Prod(k1', k2')
| Sigma(y, k1, k2) ->
    let t1 = dummy_locate (Proj(t, "fst")) in
    let k1' = single_ext k1 t1
    and k2' = single_ext (bsubst_kind k2 y t1) (dummy_locate (Proj(t, "snd"))) in
    Prod(k1', k2')

let rec try_wfsubkind env k1 k2 = match (k1, k2) with
| (Base, Base) | (Single _, Base) -> Yes
| (Arrow(k1, k2), Arrow(k1', k2')) ->
    wfsubkind env k1' k1 &*& wfsubkind env k2 k2'
| (Pi(x,k1, k2), Pi(x',k1', k2')) ->
    wfsubkind env k1' k1 &*&
    let y = new_var () in
    let y_var = dummy_locate (FVar y) in
    wfsubkind (Env.add_typ_var y k1' env)
      (bsubst_kind k2 x y_var) (bsubst_kind k2' x' y_var)
| (Arrow(k1, k2), Pi(x', k1', k2')) ->
    wfsubkind env k1' k1 &*&
    let y = new_var () in
    let y_var = dummy_locate (FVar y) in
    wfsubkind (Env.add_typ_var y k1' env) k2 (bsubst_kind k2' x' y_var)
| (Pi(x, k1, k2), Arrow(k1', k2')) ->
    wfsubkind env k1' k1 &*&
    let y = new_var () in
    let y_var = dummy_locate (FVar y) in
    wfsubkind (Env.add_typ_var y k1' env) (bsubst_kind k2 x y_var) k2'
| (Prod(k1, k2), Prod(k1', k2')) ->
    wfsubkind env k1 k1' &*& wfsubkind env k2 k2'
| (Sigma(x,k1, k2), Sigma(x',k1', k2')) ->
    wfsubkind env k1 k1 &*&
    let y = new_var () in
    let y_var = dummy_locate (FVar y) in
    wfsubkind (Env.add_typ_var y k1 env)
      (bsubst_kind k2 x y_var) (bsubst_kind k2' x' y_var)
| (Prod(k1, k2), Sigma(x',k1', k2')) ->
    wfsubkind env k1 k1 &*&
    let y = new_var () in
    let y_var = dummy_locate (FVar y) in
    wfsubkind (Env.add_typ_var y k1 env) k2 (bsubst_kind k2' x' y_var)
| (Sigma(x,k1, k2), Prod(k1', k2')) ->
    wfsubkind env k1 k1 &*&
    let y = new_var () in
    let y_var = dummy_locate (FVar y) in
    wfsubkind (Env.add_typ_var y k1 env) (bsubst_kind k2 x y_var) k2
| (Single t, Single t') ->
    let test = Normalize.equiv_typ env t t' Base in
    assert (test = Normalize.equiv_typ_simple env t t' Base) ;
    from_bool test
| _ -> No []

and wfsubkind env k1 k2 =
  match try_wfsubkind env k1 k2 with
  | Yes as yes -> yes
  | No reasons -> No ((k1, k2) :: reasons)

let wfsubkind_b env k1 k2 = Sub_result.to_bool (wfsubkind env k1 k2)

let rec wftype env t = match t.content with
| BVar _ -> assert false
| FVar x -> single_ext (Env.get_typ_var x env) t
| App(t1, t2) ->
    let k1 = wftype env t1 and k2 = wftype env t2 in 
    begin
      match k1 with
      | Arrow(k2', k1') ->
          begin
            match wfsubkind env k2 k2' with
            | Yes -> k1'
            | No reasons ->
                Error.raise_error Error.type_wf t.startpos t.endpos
                  (Printf.sprintf "Ill-kinded application:\n%s%!"
                     (subkind_error_msg reasons))
          end
      | Pi(x, k2', k1') ->
          begin
            match wfsubkind env k2 k2' with
            | Yes -> bsubst_kind k1' x t2
            | No reasons ->
                Error.raise_error Error.type_wf t.startpos t.endpos
                  (Printf.sprintf "Ill-kinded application:\n%s%!"
                     (subkind_error_msg reasons))
          end
      | _ -> Error.raise_error Error.type_wf t.startpos t.endpos
            "Non functional application."
    end
| Lam(x, k, t) ->
    if wfkind env k.content
    then
      let x' = new_var () in
      let t' = bsubst_typ t x (dummy_locate (FVar x')) in
      let k' = wftype (Env.add_typ_var x' k.content env) t' in
      Arrow(k.content, k')
    else
      Error.raise_error Error.kind_wf k.startpos k.endpos "Ill-formed kind."
| Pair(k1, k2) ->
    let k1 = wftype env k1 
    and k2 = wftype env k2 in
    Prod(k1, k2)
| Proj(t', lab) ->
    let k = wftype env t' in
    begin
      match k with
      | Prod(k1, _) | Sigma(_, k1, _) when lab = "fst" -> k1
      | Prod(_, k2) when lab = "snd" -> k2
      | Sigma(x, _, k2) when lab = "snd" ->
          bsubst_kind k2 x (dummy_locate (Proj(t', "fst")))
      | _ -> Error.raise_error Error.type_wf t.startpos t.endpos
            "Ill-formed projection."
    end
| BaseForall(x, k, u) ->
    if wfkind env k.content
    then
      let x' = new_var () in
      let u' = bsubst_typ u x (dummy_locate (FVar x')) in
      let env' = Env.add_typ_var x' k.content env in
      let k' = wftype env' u' in
      if wfsubkind_b env' k' Base 
      then Single t
      else Error.raise_error Error.type_wf k.startpos k.endpos
          "Ill-formed universal type: this kind is not a base kind."
    else Error.raise_error Error.kind_wf k.startpos k.endpos
        "Ill-formed kind."
| BaseProd(t1, t2) | BaseArrow(t1, t2) ->
    begin
      if wfsubkind_b env (wftype env t1) Base
      then if wfsubkind_b env (wftype env t2) Base
      then Single t
      else Error.raise_error Error.type_wf t2.startpos t2.endpos
          "Ill-formed basic product type: this type has not a base kind."
      else Error.raise_error Error.type_wf t1.startpos t1.endpos
          "Ill-formed basic product type: this type has not a base kind."
    end

and wfkind env = function
  | Base -> true
  | Arrow(k1, k2) | Prod(k1, k2) ->
      wfkind env k1 && wfkind env k2
  | Pi(y, k1, k2) | Sigma(y, k1, k2) ->
      wfkind env k1 &&
      let x = new_var () in
      let x_var = dummy_locate (FVar x) in
      wfkind (Env.add_typ_var x k1 env) (bsubst_kind k2 y x_var)
  | Single t ->
      match wftype env t with
      | Single _ | Base -> true
      | _ -> Error.raise_error Error.kind_wf t.startpos t.endpos
            "Ill-formed singleton: this type has not a base kind."

let wfsubtype env tau1 tau2 =
  from_bool (Normalize.equiv_typ env tau1 tau2 Base)

let wfsubtype_b env k1 k2 = Sub_result.to_bool (wfsubtype env k1 k2)
