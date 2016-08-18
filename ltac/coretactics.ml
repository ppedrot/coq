(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Locus
open Misctypes
open Genredexpr
open Constrarg
open Extraargs

open Sigma.Notations

[%%coq.plugin "coretactics"]

(** Basic tactics *)

let%coq.tacextend reflexivity = function
  [ "reflexivity" ] -> Tactics.intros_reflexivity

let%coq.tacextend exact = function
  [ "exact"; `casted_constr c ] -> Tactics.exact_no_check c

let%coq.tacextend assumption = function
  [ "assumption" ] -> Tactics.assumption

let%coq.tacextend etransitivity = function
  [ "etransitivity" ] -> Tactics.intros_transitivity None

let%coq.tacextend cut = function
  [ "cut"; `constr c ] -> Tactics.cut c

let%coq.tacextend exact_no_check = function
  [ "exact_no_check"; `constr c ] -> Tactics.exact_no_check c

let%coq.tacextend vm_cast_no_check = function
  [ "vm_cast_no_check"; `constr c ] -> Tactics.vm_cast_no_check c

let%coq.tacextend native_cast_no_check = function
  [ "native_cast_no_check"; `constr c ] -> Tactics.native_cast_no_check c

let%coq.tacextend casetype = function
  [ "casetype"; `constr c ] -> Tactics.case_type c

let%coq.tacextend elimtype = function
  [ "elimtype"; `constr c ] -> Tactics.elim_type c

let%coq.tacextend lapply = function
  [ "lapply"; `constr c ] -> Tactics.cut_and_apply c

let%coq.tacextend transitivity = function
  [ "transitivity"; `constr c ] -> Tactics.intros_transitivity (Some c)

(** Left *)

let%coq.tacextend left = function
  [ "left" ] -> Tactics.left_with_bindings false NoBindings

let%coq.tacextend eleft = function
  [ "eleft" ] -> Tactics.left_with_bindings true NoBindings

let%coq.tacextend left_with = function
  [ "left"; "with"; `bindings bl ] ->
    Tacticals.New.tclDELAYEDWITHHOLES false bl (fun bl -> Tactics.left_with_bindings false bl)

let%coq.tacextend eleft_with = function
  [ "eleft"; "with"; `bindings bl ] ->
    Tacticals.New.tclDELAYEDWITHHOLES true bl (fun bl -> Tactics.left_with_bindings true bl)

(** Right *)

let%coq.tacextend right = function
  [ "right" ] -> Tactics.right_with_bindings false NoBindings

let%coq.tacextend eright = function
  [ "eright" ] -> Tactics.right_with_bindings true NoBindings

let%coq.tacextend right_with = function
  [ "right"; "with"; `bindings bl ] ->
    Tacticals.New.tclDELAYEDWITHHOLES false bl (fun bl -> Tactics.right_with_bindings false bl)

let%coq.tacextend eright_with = function
  [ "eright"; "with"; `bindings bl ] ->
    Tacticals.New.tclDELAYEDWITHHOLES true bl (fun bl -> Tactics.right_with_bindings true bl)

(** Constructor *)

let%coq.tacextend constructor = function
  [ "constructor" ] -> Tactics.any_constructor false None
| [ "constructor"; `int_or_var i ] ->
    Tactics.constructor_tac false None i NoBindings
| [ "constructor"; `int_or_var i; "with"; `bindings bl ] ->
    let tac bl = Tactics.constructor_tac false None i bl in
    Tacticals.New.tclDELAYEDWITHHOLES false bl tac

let%coq.tacextend econstructor = function
  [ "econstructor" ] -> Tactics.any_constructor true None
| [ "econstructor"; `int_or_var i ] ->
    Tactics.constructor_tac true None i NoBindings
| [ "econstructor"; `int_or_var i; "with"; `bindings bl ] ->
    let tac bl = Tactics.constructor_tac true None i bl in
    Tacticals.New.tclDELAYEDWITHHOLES true bl tac

(** Specialize *)

let%coq.tacextend specialize = function
  [ "specialize"; `constr_with_bindings c ] ->
    Tacticals.New.tclDELAYEDWITHHOLES false c (fun c -> Tactics.specialize c None)
| [ "specialize"; `constr_with_bindings c; "as"; `intropattern ipat ] ->
    Tacticals.New.tclDELAYEDWITHHOLES false c (fun c -> Tactics.specialize c (Some ipat))

let%coq.tacextend symmetry = function
  [ "symmetry" ] -> Tactics.intros_symmetry {onhyps=Some[];concl_occs=AllOccurrences}
| [ "symmetry"; `clause_dft_concl cl ] -> Tactics.intros_symmetry cl

(** Split *)

let rec delayed_list = function
| [] -> { Tacexpr.delayed = fun _ sigma -> Sigma.here [] sigma }
| x :: l ->
  { Tacexpr.delayed = fun env sigma ->
    let Sigma (x, sigma, p) = x.Tacexpr.delayed env sigma in
    let Sigma (l, sigma, q) = (delayed_list l).Tacexpr.delayed env sigma in
    Sigma (x :: l, sigma, p +> q) }

let%coq.tacextend split = function
  [ "split" ] -> Tactics.split_with_bindings false [NoBindings]

let%coq.tacextend esplit = function
  [ "esplit" ] -> Tactics.split_with_bindings true [NoBindings]

let%coq.tacextend split_with = function
  [ "split"; "with"; `bindings bl ] ->
    Tacticals.New.tclDELAYEDWITHHOLES false bl (fun bl -> Tactics.split_with_bindings false [bl])

let%coq.tacextend esplit_with = function
  [ "esplit"; "with"; `bindings bl ] ->
    Tacticals.New.tclDELAYEDWITHHOLES true bl (fun bl -> Tactics.split_with_bindings true [bl])

let%coq.tacextend exists = function
  [ "exists" ] -> Tactics.split_with_bindings false [NoBindings]
| [ "exists"; `ne_bindings_list_sep(bll, ",") ] ->
    Tacticals.New.tclDELAYEDWITHHOLES false (delayed_list bll) (fun bll -> Tactics.split_with_bindings false bll)

let%coq.tacextend eexists = function
  [ "eexists" ] -> Tactics.split_with_bindings true [NoBindings]
| [ "eexists"; `ne_bindings_list_sep(bll, ",") ] ->
    Tacticals.New.tclDELAYEDWITHHOLES true (delayed_list bll) (fun bll -> Tactics.split_with_bindings true bll)

(** Intro *)

let%coq.tacextend intros_until = function
  [ "intros"; "until"; `quantified_hypothesis h ] -> Tactics.intros_until h

let%coq.tacextend intro = function
| [ "intro" ] -> Tactics.intro_move None MoveLast
| [ "intro"; `ident id ] -> Tactics.intro_move (Some id) MoveLast
| [ "intro"; `ident id; "at"; "top" ] -> Tactics.intro_move (Some id) MoveFirst
| [ "intro"; `ident id; "at"; "bottom" ] -> Tactics.intro_move (Some id) MoveLast
| [ "intro"; `ident id; "after"; `hyp h ] -> Tactics.intro_move (Some id) (MoveAfter h)
| [ "intro"; `ident id; "before"; `hyp h ] -> Tactics.intro_move (Some id) (MoveBefore h)
| [ "intro"; "at"; "top" ] -> Tactics.intro_move None MoveFirst
| [ "intro"; "at"; "bottom" ] -> Tactics.intro_move None MoveLast
| [ "intro"; "after"; `hyp h ] -> Tactics.intro_move None (MoveAfter h)
| [ "intro"; "before"; `hyp h ] -> Tactics.intro_move None (MoveBefore h)

(** Move *)

let%coq.tacextend move = function
  [ "move"; `hyp id; "at"; "top" ] -> Tactics.move_hyp id MoveFirst
| [ "move"; `hyp id; "at"; "bottom" ] -> Tactics.move_hyp id MoveLast
| [ "move"; `hyp id; "after"; `hyp h ] -> Tactics.move_hyp id (MoveAfter h)
| [ "move"; `hyp id; "before"; `hyp h ] -> Tactics.move_hyp id (MoveBefore h)

(** Rename *)

let%coq.tacextend rename = function
| [ "rename"; `ne_rename_list_sep(ids, ",") ] -> Tactics.rename_hyp ids

(** Revert *)

let%coq.tacextend revert = function
  [ "revert"; `ne_hyp_list hl ] -> Tactics.revert hl

(** Simple induction / destruct *)

let%coq.tacextend simple_induction = function
  [ "simple"; "induction"; `quantified_hypothesis h ] -> Tactics.simple_induct h

let%coq.tacextend simple_destruct = function
  [ "simple"; "destruct"; `quantified_hypothesis h ] -> Tactics.simple_destruct h

(** Double induction *)

let%coq.tacextend double_induction = function
  [ "double"; "induction"; `quantified_hypothesis h1; `quantified_hypothesis h2 ] ->
  Elim.h_double_induction h1 h2

(* Admit *)

let%coq.tacextend admit = function
 [ "admit" ] -> Proofview.give_up

(* Fix *)

let%coq.tacextend fix = function
  [ "fix"; `natural n ] -> Tactics.fix None n
| [ "fix"; `ident id; `natural n ] -> Tactics.fix (Some id) n

(* Cofix *)

let%coq.tacextend cofix = function
  [ "cofix" ] -> Tactics.cofix None
| [ "cofix"; `ident id ] -> Tactics.cofix (Some id)

(* Clear *)

let%coq.tacextend clear = function
  [ "clear"; `hyp_list ids ] ->
    if List.is_empty ids then Tactics.keep []
    else Tactics.clear ids
| [ "clear"; "-"; `ne_hyp_list ids ] -> Tactics.keep ids

(* Clearbody *)

let%coq.tacextend clearbody = function
  [ "clearbody"; `ne_hyp_list ids ] -> Tactics.clear_body ids

(* Generalize dependent *)

let%coq.tacextend generalize_dependent = function
  [ "generalize"; "dependent"; `constr c ] -> Tactics.generalize_dep c

(* Table of "pervasives" macros tactics (e.g. auto, simpl, etc.) *)

open Tacexpr

let initial_atomic () =
  let dloc = Loc.ghost in
  let nocl = {onhyps=Some[];concl_occs=AllOccurrences} in
  let iter (s, t) =
    let body = TacAtom (dloc, t) in
    Tacenv.register_ltac false false (Id.of_string s) body
  in
  let () = List.iter iter
      [ "red", TacReduce(Red false,nocl);
        "hnf", TacReduce(Hnf,nocl);
        "simpl", TacReduce(Simpl (Redops.all_flags,None),nocl);
        "compute", TacReduce(Cbv Redops.all_flags,nocl);
        "intros", TacIntroPattern (false,[]);
      ]
  in
  let iter (s, t) = Tacenv.register_ltac false false (Id.of_string s) t in
  List.iter iter
      [ "idtac",TacId [];
        "fail", TacFail(TacLocal,ArgArg 0,[]);
        "fresh", TacArg(dloc,TacFreshId [])
      ]

let () = Mltop.declare_cache_obj initial_atomic "coretactics"
