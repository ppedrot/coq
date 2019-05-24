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
open Univ
open Constr
open Mod_subst

type work_list = (Instance.t * Id.t array) Cmap.t * 
  (Instance.t * Id.t array) Mindmap.t

type indirect_accessor = {
  access_proof : DirPath.t -> int -> constr option;
  access_digest : Digest.t -> constr;
  access_constraints : DirPath.t -> int -> Univ.ContextSet.t option;
}

type cooking_info = { 
  modlist : work_list; 
  abstract : Constr.named_context * Univ.Instance.t * Univ.AUContext.t }
type proofterm = (constr * Univ.ContextSet.t) Future.computation
type opaque =
  | Indirect of substitution list * DirPath.t * int (* subst, lib, index *)
  | Direct of cooking_info list * proofterm

type indirect =
| InMemory of proofterm
| Serialized of Digest.t * Univ.ContextSet.t

type opaquetab = {
  opaque_val : (cooking_info list * indirect) Int.Map.t;
  (** Actual proof terms *)
  opaque_len : int;
  (** Size of the above map *)
  opaque_dir : DirPath.t;
  opaque_prg : Int.Set.t;
  (** Subset of [opaque_val] that has to be purged *)
}
let empty_opaquetab = {
  opaque_val = Int.Map.empty;
  opaque_len = 0;
  opaque_dir = DirPath.initial;
  opaque_prg = Int.Set.empty;
}

let not_here () =
  CErrors.user_err Pp.(str "Cannot access opaque delayed proof")

let create cu = Direct ([],cu)

let turn_indirect dp o tab = match o with
  | Indirect (_,_,i) ->
      if not (Int.Map.mem i tab.opaque_val)
      then CErrors.anomaly (Pp.str "Indirect in a different table.")
      else CErrors.anomaly (Pp.str "Already an indirect opaque.")
  | Direct (d,cu) ->
    (* Invariant: direct opaques only exist inside sections, we turn them
      indirect as soon as we are at toplevel. At this moment, we perform
      hashconsing of their contents, potentially as a future. *)
      let id = tab.opaque_len in
      let opaque_val = Int.Map.add id (d, InMemory cu) tab.opaque_val in
      let opaque_prg = Int.Set.add id tab.opaque_prg in
      let opaque_dir =
        if DirPath.equal dp tab.opaque_dir then tab.opaque_dir
        else if DirPath.equal tab.opaque_dir DirPath.initial then dp
        else CErrors.anomaly
          (Pp.str "Using the same opaque table for multiple dirpaths.") in
      let ntab = { opaque_val; opaque_prg; opaque_dir; opaque_len = id + 1 } in
      Indirect ([],dp,id), ntab

let purge_indirect tab =
  let fold i (purge, vals, ans as accu) =
    let (ci, pf) = match Int.Map.find i vals with
    | ci, InMemory pf -> (ci, pf)
    | _, Serialized _ -> assert false
    | exception Not_found -> assert false
    in
    if Future.is_val pf then
      let (c, u) = Future.force pf in
      let purge = Int.Set.remove i purge in
      let c = Marshal.to_string c [] in
      let digest = Digest.string c in
      let vals = Int.Map.add i (ci, Serialized (digest, u)) vals in
      (purge, vals, (tab.opaque_dir, i, c) :: ans)
    else
      accu
  in
  let (opaque_prg, opaque_val, ans) = Int.Set.fold fold tab.opaque_prg (tab.opaque_prg, tab.opaque_val, []) in
  { tab with opaque_val; opaque_prg }, ans

let subst_opaque sub = function
  | Indirect (s,dp,i) -> Indirect (sub::s,dp,i)
  | Direct _ -> CErrors.anomaly (Pp.str "Substituting a Direct opaque.")

let discharge_direct_opaque ~cook_constr ci = function
  | Indirect _ -> CErrors.anomaly (Pp.str "Not a direct opaque.")
  | Direct (d,cu) ->
      Direct (ci::d,Future.chain cu (fun (c, u) -> cook_constr c, u))

let join except cu = match except with
| None -> ignore (Future.join cu)
| Some except ->
  if Future.UUIDSet.mem (Future.uuid cu) except then ()
  else ignore (Future.join cu)

let join_opaque ?except { opaque_val = prfs; opaque_dir = odp; _ } = function
  | Direct (_,cu) -> join except cu
  | Indirect (_,dp,i) ->
      if DirPath.equal dp odp then
        let fp = snd (Int.Map.find i prfs) in
        match fp with
        | InMemory fp -> join except fp
        | Serialized _ -> ()

let force_proof access { opaque_val = prfs; opaque_dir = odp; _ } = function
  | Direct (_,cu) ->
      fst(Future.force cu)
  | Indirect (l,dp,i) ->
      let c =
        if DirPath.equal dp odp then
        match snd (Int.Map.find i prfs) with
        | InMemory pf -> fst (Future.force pf)
        | Serialized (d, _) -> access.access_digest d
        else match access.access_proof dp i with
        | None -> not_here ()
        | Some v -> v
      in
      force_constr (List.fold_right subst_substituted l (from_val c))

let force_constraints access { opaque_val = prfs; opaque_dir = odp; _ } = function
  | Direct (_,cu) -> snd(Future.force cu)
  | Indirect (_,dp,i) ->
      if DirPath.equal dp odp then
      match snd (Int.Map.find i prfs) with
      | InMemory pf -> snd (Future.force pf)
      | Serialized (_, u) -> u
      else match access.access_constraints dp i with
        | None -> Univ.ContextSet.empty
        | Some u -> u

let get_direct_constraints = function
| Indirect _ -> CErrors.anomaly (Pp.str "Not a direct opaque.")
| Direct (_, cu) -> Future.chain cu snd

module FMap = Future.UUIDMap

let dump ?(except = Future.UUIDSet.empty) { opaque_val = otab; opaque_len = n; _ } =
  let opaque_table = Array.make n None in
  let univ_table = Array.make n None in
  let disch_table = Array.make n [] in
  let f2t_map = ref FMap.empty in
  let iter n (d, cu) = match cu with
  | InMemory cu ->
    let uid = Future.uuid cu in
    let () = f2t_map := FMap.add (Future.uuid cu) n !f2t_map in
    if Future.is_val cu then
      let (c, u) = Future.force cu in
      let () = univ_table.(n) <- Some u in
      opaque_table.(n) <- Some (Util.Inl c)
    else if Future.UUIDSet.mem uid except then
      disch_table.(n) <- d
    else
      CErrors.anomaly
        Pp.(str"Proof object "++int n++str" is not checked nor to be checked")
  | Serialized (d, u) ->
    (* Don't store the term, this will be done by Library *)
    let () = univ_table.(n) <- Some u in
    opaque_table.(n) <- Some (Util.Inr d)
  in
  let () = Int.Map.iter iter otab in
  opaque_table, univ_table, disch_table, !f2t_map
