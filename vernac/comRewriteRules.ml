(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Entries
open Constrintern

let add ul bl lhs rhs =
  let env = Global.env () in
  let evd, decl = Constrexpr_ops.interp_univ_decl env ul in
  let evd, (impls, ((env_bl, ctx), imps1)) = interp_context_evars env evd bl in
  let evd, lhs, ty =
    let expected_type = Pretyping.WithoutTypeConstraint in
    let lhs = intern_gen expected_type ~impls env_bl evd lhs in
    let flags = Pretyping.all_no_fail_flags in
    Pretyping.understand_tcc_ty ~flags env_bl evd ~expected_type lhs
  in
  let evd, rhs = interp_casted_constr_evars ~impls env_bl evd rhs ty in
  let evd = Evd.minimize_universes evd in
  let nf c = EConstr.to_constr ~abort_on_undefined_evars:false evd c in
  let ctx = List.map Termops.(map_rel_decl nf) ctx in
  let lhs = nf lhs in
  let rhs = nf rhs in
  (* Keep only useful universes. *)
  let uvars_fold uvars c =
    Univ.LSet.union uvars (EConstr.universes_of_constr evd (EConstr.of_constr c))
  in
  let uvars = List.fold_left uvars_fold Univ.LSet.empty
    [Term.it_mkLambda_or_LetIn Constr.mkProp ctx; lhs; rhs]
  in
  let evd = Evd.restrict_universe_context evd uvars in
  (* Check we conform to declared universes *)
  let uctx = Evd.check_univ_decl ~poly:true evd decl in
  let (inst, uctx) = match uctx with
  | Polymorphic_entry (nas, uctx) ->
    Univ.abstract_universes nas uctx
  | Monomorphic_entry _ -> assert false
  in
  let sbst = Univ.make_instance_subst inst in
  let lhs = Vars.subst_univs_level_constr sbst lhs in
  let rhs = Vars.subst_univs_level_constr sbst rhs in
  let ctx = Vars.subst_univs_level_context sbst ctx in
  let r = {
    rwrule_univs = uctx;
    rwrule_context = ctx;
    rwrule_lhs = lhs;
    rwrule_rhs = rhs;
  } in
  Declare.declare_rewrite_rule r
