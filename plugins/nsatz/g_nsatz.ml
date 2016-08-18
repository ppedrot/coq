(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

[%%coq.plugin "nsatz_plugin"]

let%coq.tacextend nsatz_compute = function
| [ "nsatz_compute";  `constr(lt) ] -> Nsatz.nsatz_compute lt
