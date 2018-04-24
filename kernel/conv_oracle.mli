(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

type oracle

val empty : oracle
(** Warning: empty oracle means everything is transparent. *)

val all_opaque : oracle
val var_transparent : oracle
val cst_transparent : oracle

(** Order on section paths for unfolding.
   If [oracle_order kn1 kn2] is true, then unfold kn1 first.
   Note: the oracle does not introduce incompleteness, it only
   tries to postpone unfolding of "opaque" constants. *)
val oracle_order : ('a -> Constant.t) -> oracle -> bool -> 
  'a tableKey -> 'a tableKey -> bool

(** Priority for the expansion of constant in the conversion test.
 * Higher levels means that the expansion is less prioritary.
 * (And Expand stands for -oo, and Opaque +oo.)
 * The default value (transparent constants) is [Level 0].
 *)
type level = Expand | Level of int | Opaque
val transparent : level

(** Check whether a level is [Level 0] *)
val is_transparent : level -> bool

val get_strategy : oracle -> Constant.t tableKey -> level

(** Sets the level of a constant.
 * Level of RelKey constant cannot be set. *)
val set_strategy : oracle -> Constant.t tableKey -> level -> oracle

(** Fold over the non-default levels of the oracle. Order unspecified. *)
val fold_strategy : (Constant.t tableKey -> level -> 'a -> 'a) -> oracle -> 'a -> 'a

val set_transparent_variable : oracle -> variable -> oracle
(** Same as [set_strategy oracle (VarKey id) (Level 0)] *)

val set_transparent_constant : oracle -> Constant.t -> oracle
(** Same as [set_strategy oracle (ConstKey cst) (Level 0)] *)

val set_opaque_variable : oracle -> variable -> oracle
(** Same as [set_strategy oracle (VarKey id) Opaque] *)

val set_opaque_constant : oracle -> Constant.t -> oracle
(** Same as [set_strategy oracle (ConstKey cst) Opaque] *)

val is_transparent_variable : oracle -> variable -> bool
(** Same as [get_strategy oracle (VarKey id) != Opaque] *)

val is_transparent_constant : oracle -> Constant.t -> bool
(** Same as [get_strategy oracle (ConstKey cst) != Opaque] *)

(** {5 Legacy code} *)

val is_all_opaque : oracle -> bool
(** Only used by legacy unification / auto *)

val subset : oracle -> oracle -> bool
(** Only used by legacy unification *)
