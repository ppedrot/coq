(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Bruno Barras as part of the rewriting of the conversion
   algorithm, Nov 2001 *)

open Names

(* Priority for the expansion of constant in the conversion test.
 * Higher levels means that the expansion is less prioritary.
 * (And Expand stands for -oo, and Opaque +oo.)
 * The default value is [Level 100].
 *)
type level = Expand | Level of int | Opaque
let default = Level 0
let transparent = default
let is_transparent = function
| Level 0 -> true
| _ -> false
let is_default_or_opaque = function
| Level 0 -> true
| Opaque -> true
| _ -> false

type oracle = {
  var_opacity : level Id.Map.t;
  cst_opacity : level Cmap.t;
  var_trstate : Id.Pred.t;
  cst_trstate : Cpred.t;
}
(** Invariants:
    - No variable binds to [Level 0] or [Opaque] in [var_opacity]
    - If a variable is bound in [var_opacity] then it is also in [var_trstate]
    - Similarly for constants *)

let empty = {
  var_opacity = Id.Map.empty;
  cst_opacity = Cmap.empty;
  var_trstate = Id.Pred.full;
  cst_trstate = Cpred.full;
}

let all_opaque = {
  var_opacity = Id.Map.empty;
  cst_opacity = Cmap.empty;
  var_trstate = Id.Pred.empty;
  cst_trstate = Cpred.empty;
}

let var_transparent = { all_opaque with var_trstate = Id.Pred.full }
let cst_transparent = { all_opaque with cst_trstate = Cpred.full }

let get_strategy { var_opacity; cst_opacity; var_trstate; cst_trstate } f = function
  | VarKey id ->
      (try Id.Map.find id var_opacity
      with Not_found -> if Id.Pred.mem id var_trstate then default else Opaque)
  | ConstKey c ->
      let c = f c in
      (try Cmap.find c cst_opacity
      with Not_found -> if Cpred.mem c cst_trstate then default else Opaque)
  | RelKey _ -> Expand

let set_strategy ({ var_opacity; cst_opacity } as oracle) k l =
  match k with
  | VarKey id ->
    let var_opacity =
      if is_default_or_opaque l then Id.Map.remove id var_opacity
      else Id.Map.add id l var_opacity
    in
    let var_trstate = match l with
    | Opaque -> Id.Pred.remove id oracle.var_trstate
    | _ -> Id.Pred.add id oracle.var_trstate
    in
    { oracle with var_opacity; var_trstate; }
  | ConstKey c ->
    let cst_opacity =
      if is_default_or_opaque l then Cmap.remove c cst_opacity
      else Cmap.add c l cst_opacity
    in
    let cst_trstate = match l with
    | Opaque -> Cpred.remove c oracle.cst_trstate
    | _ -> Cpred.add c oracle.cst_trstate
    in
    { oracle with cst_opacity; cst_trstate; }
  | RelKey _ -> CErrors.user_err Pp.(str "set_strategy: RelKey")

let fold_strategy f { var_opacity; var_trstate; cst_opacity; cst_trstate; } accu =
  let fvar id lvl accu = f (VarKey id) lvl accu in
  let fcst cst lvl accu = f (ConstKey cst) lvl accu in
  let accu = Id.Map.fold fvar var_opacity accu in
  let accu = Cmap.fold fcst cst_opacity accu in
  let fvar accu id = f (VarKey id) Opaque accu in
  let (neg, elts) = Id.Pred.elements var_trstate in
  let accu = if neg then List.fold_left fvar accu elts else accu in
  let fcst accu cst = f (ConstKey cst) Opaque accu in
  let (neg, elts) = Cpred.elements cst_trstate in
  if neg then List.fold_left fcst accu elts else accu

(* Unfold the first constant only if it is "more transparent" than the
   second one. In case of tie, use the recommended default. *)
let oracle_order f o l2r k1 k2 =
  match get_strategy o f k1, get_strategy o f k2 with
  | Expand, Expand -> l2r
  | Expand, (Opaque | Level _) -> true
  | (Opaque | Level _), Expand -> false
  | Opaque, Opaque -> l2r
  | Level _, Opaque -> true
  | Opaque, Level _ -> false
  | Level n1, Level n2 ->
     if Int.equal n1 n2 then l2r
     else n1 < n2

let get_strategy o = get_strategy o (fun x -> x)

let set_transparent_constant oracle cst =
  set_strategy oracle (ConstKey cst) default

let set_transparent_variable oracle id =
  set_strategy oracle (VarKey id) default

let set_opaque_constant oracle cst =
  set_strategy oracle (ConstKey cst) Opaque

let set_opaque_variable oracle id =
  set_strategy oracle (VarKey id) Opaque

let is_transparent_variable o id =
  Id.Pred.mem id o.var_trstate

let is_transparent_constant o c =
  Cpred.mem c o.cst_trstate

(** Legacy code *)

let is_all_opaque o =
  (** No need to check for the two other fields due to invariant *)
  Id.Pred.is_empty o.var_trstate && Cpred.is_empty o.cst_trstate

let subset o1 o2 =
  Id.Pred.subset o1.var_trstate o2.var_trstate
    && Cpred.subset o1.cst_trstate o2.cst_trstate
