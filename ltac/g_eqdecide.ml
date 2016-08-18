(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(*                              EqDecide                               *)
(*   A tactic for deciding propositional equality on inductive types   *)
(*                           by Eduardo Gimenez                        *)
(************************************************************************)

open Eqdecide

[%%coq.plugin "g_eqdecide"]

let%coq.tacextend decide_equality = function
| [ "decide"; "equality" ] -> decideEqualityGoal

let%coq.tacextend compare = function
| [ "compare"; `constr(c1); `constr(c2) ] -> compare c1 c2
