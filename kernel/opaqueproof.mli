(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Mod_subst

(** This module implements the handling of opaque proof terms.
    Opaque proof terms are special since:
    - they can be lazily computed and substituted
    - they are stored in an optionally loaded segment of .vo files
    An [opaque] proof terms holds an index into an opaque table. *)

type 'a delayed_universes =
| PrivateMonomorphic of 'a * Univ.ContextSet.t
| PrivatePolymorphic of int * Univ.ContextSet.t
  (** Number of surrounding bound universes + local constraints *)

type proofterm = (constr * Univ.Constraints.t delayed_universes) Future.computation
type opaquetab
type 'cooking_info opaque

val empty_opaquetab : opaquetab

(** From a [proofterm] to some [opaque]. *)
val create : DirPath.t -> proofterm -> opaquetab -> 'c opaque * opaquetab

type opaque_proofterm = Constr.t * unit delayed_universes

type opaque_handle

type 'cooking_info indirect_accessor = {
  access_proof : DirPath.t -> opaque_handle -> opaque_proofterm option;
  access_discharge : 'cooking_info list -> opaque_proofterm -> opaque_proofterm;
}
(** Opaque terms are indexed by their library
    dirpath and an integer index. The two functions above activate
    this indirect storage, by telling how to retrieve terms.
*)

(** From a [opaque] back to a [constr]. This might use the
    indirect opaque accessor given as an argument. *)
val force_proof : 'c indirect_accessor -> opaquetab -> 'c opaque -> opaque_proofterm
val force_constraints : 'c indirect_accessor -> opaquetab -> 'c opaque -> Univ.Constraints.t

val subst_opaque : substitution -> 'c opaque -> 'c opaque

val discharge_opaque :
  'cooking_info -> 'cooking_info opaque -> 'cooking_info opaque

val join_opaque : ?except:Future.UUIDSet.t -> opaquetab -> 'c opaque -> unit

(** {5 Serialization} *)

type opaque_disk

val dump : ?except:Future.UUIDSet.t -> opaquetab -> opaque_disk * opaque_handle Future.UUIDMap.t

val get_opaque_disk : opaque_handle -> opaque_disk -> opaque_proofterm option
val set_opaque_disk : opaque_handle -> opaque_proofterm -> opaque_disk -> unit

(** Only used for pretty-printing *)
val repr_handle : opaque_handle -> int
