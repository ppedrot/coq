(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Bruno Barras with Benjamin Werner's account to implement
   a call-by-value conversion algorithm and a lazy reduction machine
   with sharing, Nov 1996 *)
(* Addition of zeta-reduction (let-in contraction) by Hugo Herbelin, Oct 2000 *)
(* Call-by-value machine moved to cbv.ml, Mar 01 *)
(* Additional tools for module subtyping by Jacek Chrzaszcz, Aug 2002 *)
(* Extension with closure optimization by Bruno Barras, Aug 2003 *)
(* Support for evar reduction by Bruno Barras, Feb 2009 *)
(* Miscellaneous other improvements by Bruno Barras, 1997-2009 *)

(* This file implements a lazy reduction for the Calculus of Inductive
   Constructions *)

[@@@ocaml.warning "+4"]

open CErrors
open Util
open Pp
open Names
open Constr
open Vars
open Environ
open Esubst

let stats = ref false

(* Profiling *)
let beta = ref 0
let delta = ref 0
let eta = ref 0
let zeta = ref 0
let evar = ref 0
let nb_match = ref 0
let fix = ref 0
let cofix = ref 0
let prune = ref 0

let reset () =
  beta := 0; delta := 0; zeta := 0; evar := 0; nb_match := 0; fix := 0;
  cofix := 0; evar := 0; prune := 0

let stop() =
  Feedback.msg_debug (str "[Reds: beta=" ++ int !beta ++ str" delta=" ++ int !delta ++
         str " eta=" ++ int !eta ++ str" zeta=" ++ int !zeta ++ str" evar=" ++
         int !evar ++ str" match=" ++ int !nb_match ++ str" fix=" ++ int !fix ++
         str " cofix=" ++ int !cofix ++ str" prune=" ++ int !prune ++
         str"]")

let incr_cnt red cnt =
  if red then begin
    if !stats then incr cnt;
    true
  end else
    false

let with_stats c =
  if !stats then begin
    reset();
    let r = Lazy.force c in
    stop();
    r
  end else
    Lazy.force c

let all_opaque = TransparentState.empty
let all_transparent = TransparentState.full

module type RedFlagsSig = sig
  type reds
  type red_kind
  val fBETA : red_kind
  val fDELTA : red_kind
  val fETA : red_kind
  val fMATCH : red_kind
  val fFIX : red_kind
  val fCOFIX : red_kind
  val fZETA : red_kind
  val fCONST : Constant.t -> red_kind
  val fVAR : Id.t -> red_kind
  val no_red : reds
  val red_add : reds -> red_kind -> reds
  val red_sub : reds -> red_kind -> reds
  val red_add_transparent : reds -> TransparentState.t -> reds
  val red_transparent : reds -> TransparentState.t
  val mkflags : red_kind list -> reds
  val red_set : reds -> red_kind -> bool
  val red_projection : reds -> Projection.t -> bool
end

module RedFlags = (struct

  (* [r_const=(true,cl)] means all constants but those in [cl] *)
  (* [r_const=(false,cl)] means only those in [cl] *)
  (* [r_delta=true] just mean [r_const=(true,[])] *)

  open TransparentState

  type reds = {
    r_beta : bool;
    r_delta : bool;
    r_eta : bool;
    r_const : TransparentState.t;
    r_zeta : bool;
    r_match : bool;
    r_fix : bool;
    r_cofix : bool }

  type red_kind = BETA | DELTA | ETA | MATCH | FIX
              | COFIX | ZETA
              | CONST of Constant.t | VAR of Id.t
  let fBETA = BETA
  let fDELTA = DELTA
  let fETA = ETA
  let fMATCH = MATCH
  let fFIX = FIX
  let fCOFIX = COFIX
  let fZETA = ZETA
  let fCONST kn  = CONST kn
  let fVAR id  = VAR id
  let no_red = {
    r_beta = false;
    r_delta = false;
    r_eta = false;
    r_const = all_opaque;
    r_zeta = false;
    r_match = false;
    r_fix = false;
    r_cofix = false }

  let red_add red = function
    | BETA -> { red with r_beta = true }
    | ETA -> { red with r_eta = true }
    | DELTA -> { red with r_delta = true; r_const = all_transparent }
    | CONST kn ->
      let r = red.r_const in
      { red with r_const = { r with tr_cst = Cpred.add kn r.tr_cst } }
    | MATCH -> { red with r_match = true }
    | FIX -> { red with r_fix = true }
    | COFIX -> { red with r_cofix = true }
    | ZETA -> { red with r_zeta = true }
    | VAR id ->
      let r = red.r_const in
      { red with r_const = { r with tr_var = Id.Pred.add id r.tr_var } }

  let red_sub red = function
    | BETA -> { red with r_beta = false }
    | ETA -> { red with r_eta = false }
    | DELTA -> { red with r_delta = false }
    | CONST kn ->
      let r = red.r_const in
      { red with r_const = { r with tr_cst = Cpred.remove kn r.tr_cst } }
    | MATCH -> { red with r_match = false }
    | FIX -> { red with r_fix = false }
    | COFIX -> { red with r_cofix = false }
    | ZETA -> { red with r_zeta = false }
    | VAR id ->
      let r = red.r_const in
      { red with r_const = { r with tr_var = Id.Pred.remove id r.tr_var } }

  let red_transparent red = red.r_const

  let red_add_transparent red tr =
    { red with r_const = tr }

  let mkflags = List.fold_left red_add no_red

  let red_set red = function
    | BETA -> incr_cnt red.r_beta beta
    | ETA -> incr_cnt red.r_eta eta
    | CONST kn ->
      let c = is_transparent_constant red.r_const kn in
        incr_cnt c delta
    | VAR id -> (* En attendant d'avoir des kn pour les Var *)
      let c = is_transparent_variable red.r_const id in
        incr_cnt c delta
    | ZETA -> incr_cnt red.r_zeta zeta
    | MATCH -> incr_cnt red.r_match nb_match
    | FIX -> incr_cnt red.r_fix fix
    | COFIX -> incr_cnt red.r_cofix cofix
    | DELTA -> (* Used for Rel/Var defined in context *)
        incr_cnt red.r_delta delta

  let red_projection red p =
    if Projection.unfolded p then true
    else red_set red (fCONST (Projection.constant p))

end : RedFlagsSig)

open RedFlags

let all = mkflags [fBETA;fDELTA;fZETA;fMATCH;fFIX;fCOFIX]
let allnolet = mkflags [fBETA;fDELTA;fMATCH;fFIX;fCOFIX]
let beta = mkflags [fBETA]
let betadeltazeta = mkflags [fBETA;fDELTA;fZETA]
let betaiota = mkflags [fBETA;fMATCH;fFIX;fCOFIX]
let betaiotazeta = mkflags [fBETA;fMATCH;fFIX;fCOFIX;fZETA]
let betazeta = mkflags [fBETA;fZETA]
let delta = mkflags [fDELTA]
let zeta = mkflags [fZETA]
let nored = no_red

(* Removing fZETA for finer behaviour would break many developments *)
let unfold_side_flags = [fBETA;fMATCH;fFIX;fCOFIX;fZETA]
let unfold_side_red = mkflags [fBETA;fMATCH;fFIX;fCOFIX;fZETA]
let unfold_red kn =
  let flag = match kn with
    | EvalVarRef id -> fVAR id
    | EvalConstRef kn -> fCONST kn in
  mkflags (flag::unfold_side_flags)

(* Flags of reduction and cache of constants: 'a is a type that may be
 * mapped to constr. 'a infos implements a cache for constants and
 * abstractions, storing a representation (of type 'a) of the body of
 * this constant or abstraction.
 *  * i_tab is the cache table of the results
 *
 * ref_value_cache searchs in the tab, otherwise uses i_repr to
 * compute the result and store it in the table. If the constant can't
 * be unfolded, returns None, but does not store this failure.  * This
 * doesn't take the RESET into account. You mustn't keep such a table
 * after a Reset.  * This type is not exported. Only its two
 * instantiations (cbv or lazy) are.
 *)

type table_key = Constant.t Univ.puniverses tableKey

let eq_pconstant_key (c,u) (c',u') =
  eq_constant_key c c' && Univ.Instance.equal u u'

module IdKeyHash =
struct
  open Hashset.Combine
  type t = table_key
  let equal = Names.eq_table_key eq_pconstant_key
  let hash = function
  | ConstKey (c, _) -> combinesmall 1 (Constant.UserOrd.hash c)
  | VarKey id -> combinesmall 2 (Id.hash id)
  | RelKey i -> combinesmall 3 (Int.hash i)
end

module KeyTable = Hashtbl.Make(IdKeyHash)

open Context.Named.Declaration

let assoc_defined id env = match Environ.lookup_named id env with
| LocalDef (_, c, _) -> c
| LocalAssum _ -> raise Not_found

(**********************************************************************)
(* Lazy reduction: the one used in kernel operations                  *)

(* type of shared terms. fconstr and frterm are mutually recursive.
 * Clone of the constr structure, but completely mutable, and
 * annotated with reduction state (reducible or not).
 *  - FLIFT is a delayed shift; allows sharing between 2 lifted copies
 *    of a given term.
 *  - FCLOS is a delayed substitution applied to a constr
 *  - FLOCK is used to erase the content of a reference that must
 *    be updated. This is to allow the garbage collector to work
 *    before the term is computed.
 *)

(* Norm means the term is fully normalized and cannot create a redex
     when substituted
   Cstr means the term is in head normal form and that it can
     create a redex when substituted (i.e. constructor, fix, lambda)
   Whnf means we reached the head normal form and that it cannot
     create a redex when substituted
   Red is used for terms that might be reduced
*)
type red_state = Norm | Cstr | Whnf | Red

type fconstr = { mutable term: fshape }

and fshape =
| FCLOS of constr * fconstr subs
| FEVAL of fterm * stack * red_state
| FLIFT of fconstr * int
| FLOCK

and fterm =
  | FRel of int
  | FAtom of constr (* Metas and Sorts *)
  | FFlex of table_key
  | FInd of pinductive
  | FConstruct of pconstructor
  | FProj of Projection.t * fconstr
  | FFix of fixpoint * fconstr subs
  | FCoFix of cofixpoint * fconstr subs
  | FLambda of int * (Name.t * constr) list * constr * fconstr subs
  | FProd of Name.t * fconstr * constr * fconstr subs
  | FLetIn of Name.t * fconstr * fconstr * constr * fconstr subs
  | FEvar of existential * fconstr subs

(**********************************************************************)
(* The type of (machine) stacks (= lambda-bar-calculus' contexts)     *)

and stack_member =
  | Zapp of fconstr array
  | ZcaseT of case_info * constr * constr array * fconstr subs
  | Zproj of Projection.Repr.t
  | Zfix of fixpoint * fconstr subs * stack
  | Zshift of int

and stack = stack_member list

(** Reduction cache *)

type infos_cache = {
  i_env : env;
  i_sigma : existential -> constr option;
  i_share : bool;
}

type clos_infos = {
  i_flags : reds;
  i_cache : infos_cache }

type clos_tab = fconstr KeyTable.t

let info_flags info = info.i_flags
let info_env info = info.i_cache.i_env

let empty_stack = []
let append_stack v s =
  if Int.equal (Array.length v) 0 then s else
  match s with
  | Zapp l :: s -> Zapp (Array.append v l) :: s
  | (ZcaseT _ | Zproj _ | Zfix _ | Zshift _) :: _ | [] ->
    Zapp v :: s

let rec stack_args_size = function
  | Zapp v :: s -> Array.length v + stack_args_size s
  | Zshift(_)::s -> stack_args_size s
  | (ZcaseT _ | Zproj _ | Zfix _) :: _ | [] -> 0

let lft_fconstr n ft = { term = FLIFT (ft, n) }
let lift_fconstr k f =
  if Int.equal k 0 then f else lft_fconstr k f
let lift_fconstr_vect k v =
  if Int.equal k 0 then v else Array.Fun1.map lft_fconstr k v

let clos_rel e i =
  match expand_rel i e with
    | Inl(n,mt) -> lift_fconstr n mt
    | Inr(k,None) ->
      { term = FEVAL (FRel k, [], Norm) }
    | Inr(k,Some p) ->
      lift_fconstr (k-p) { term = FEVAL (FFlex(RelKey p), [], Red) }

let mk_lambda env t =
  let (rvars,t') = Term.decompose_lam t in
  FLambda(List.length rvars, List.rev rvars, t', env)

let mk_shape n t = { term = FEVAL (t, [], n) }

let fterm_of m = match m.term with
| FEVAL (m, [], _) -> m
| FLOCK | FCLOS _ | FEVAL _ | FLIFT _ ->
  assert false (** assumes the term to be reduced *)

(* Optimization: do not enclose variables in a closure.
   Makes variable access much faster *)
let mk_clos e t =
  match kind t with
    | Rel i -> clos_rel e i
    | Var x -> mk_shape Red (FFlex (VarKey x))
    | Const c -> mk_shape Red (FFlex (ConstKey c))
    | Meta _ | Sort _ ->  mk_shape Norm (FAtom t)
    | Ind kn -> mk_shape Norm (FInd kn)
    | Construct kn -> mk_shape Cstr (FConstruct kn)
    | (CoFix _|Lambda _|Fix _|Prod _|Evar _|App _|Case _|Cast _|LetIn _|Proj _) ->
        { term = FCLOS(t,e) }

let inject c = mk_clos (subs_id 0) c

let destFLambda t =
  match [@ocaml.warning "-4"] fterm_of t with
  | FLambda(_,[(na,ty)],b,e) -> (na,mk_clos e ty,mk_clos (subs_lift e) b)
  | FLambda(n,(na,ty)::tys,b,e) ->
    (na,mk_clos e ty,{ term = FEVAL (FLambda(n-1,tys,b,subs_lift e), [], Cstr) })
  | _ -> assert false
(* t must be a FLambda and binding list cannot be empty *)

(** Hand-unrolling of the map function to bypass the call to the generic array
    allocation *)
let mk_clos_vect env v = match v with
| [||] -> [||]
| [|v0|] -> [|mk_clos env v0|]
| [|v0; v1|] -> [|mk_clos env v0; mk_clos env v1|]
| [|v0; v1; v2|] -> [|mk_clos env v0; mk_clos env v1; mk_clos env v2|]
| [|v0; v1; v2; v3|] ->
  [|mk_clos env v0; mk_clos env v1; mk_clos env v2; mk_clos env v3|]
| v -> Array.Fun1.map mk_clos env v

let ref_value_cache ({ i_cache = cache; _ }) tab ref =
  try
    Some (KeyTable.find tab ref)
  with Not_found ->
  try
    let body =
      match ref with
        | RelKey n ->
          let open! Context.Rel.Declaration in
          let i = n - 1 in
          let (d, _) =
            try Range.get cache.i_env.env_rel_context.env_rel_map i
            with Invalid_argument _ -> raise Not_found
          in
          begin match d with
          | LocalAssum _ -> raise Not_found
          | LocalDef (_, t, _) -> lift n t
          end
        | VarKey id -> assoc_defined id cache.i_env
        | ConstKey cst -> constant_value_in cache.i_env cst
    in
    let v = inject body in
    KeyTable.add tab ref v;
    Some v
  with
    | Not_found (* List.assoc *)
    | NotEvaluableConst _ (* Const *)
      -> None

(* The inverse of mk_clos: move back to constr *)
let rec to_constr lfts v =
  match v.term with
  | FCLOS (t, env) ->
    if is_subs_id env && is_lift_id lfts then t
    else
      let subs = comp_subs lfts env in
      subst_constr subs t
  | FEVAL (_t, _stk, _) ->
    assert false
  | FLIFT (_t, _k) ->
    assert false
  | FLOCK -> assert false

and _fto_constr lfts = function
    | FRel i -> mkRel (reloc_rel i lfts)
    | FFlex (RelKey p) -> mkRel (reloc_rel p lfts)
    | FFlex (VarKey x) -> mkVar x
    | FAtom c -> exliftn lfts c
    | FFlex (ConstKey op) -> mkConstU op
    | FInd op -> mkIndU op
    | FConstruct op -> mkConstructU op
    | FFix ((op,(lna,tys,bds)) as fx, e) ->
      if is_subs_id e && is_lift_id lfts then
        mkFix fx
      else
        let n = Array.length bds in
        let subs_ty = comp_subs lfts e in
        let subs_bd = comp_subs (el_liftn n lfts) (subs_liftn n e) in
        let tys = Array.Fun1.map subst_constr subs_ty tys in
        let bds = Array.Fun1.map subst_constr subs_bd bds in
        mkFix (op, (lna, tys, bds))
    | FCoFix ((op,(lna,tys,bds)) as cfx, e) ->
      if is_subs_id e && is_lift_id lfts then
        mkCoFix cfx
      else
        let n = Array.length bds in
        let subs_ty = comp_subs lfts e in
        let subs_bd = comp_subs (el_liftn n lfts) (subs_liftn n e) in
        let tys = Array.Fun1.map subst_constr subs_ty tys in
        let bds = Array.Fun1.map subst_constr subs_bd bds in
        mkCoFix (op, (lna, tys, bds))
    | FProj (p,c) ->
        mkProj (p,to_constr lfts c)

    | FLambda (len, tys, f, e) ->
      if is_subs_id e && is_lift_id lfts then
        Term.compose_lam (List.rev tys) f
      else
        let subs = comp_subs lfts e in
        let tys = List.mapi (fun i (na, c) -> na, subst_constr (subs_liftn i subs) c) tys in
        let f = subst_constr (subs_liftn len subs) f in
        Term.compose_lam (List.rev tys) f
    | FProd (n, t, c, e) ->
      if is_subs_id e && is_lift_id lfts then
        mkProd (n, to_constr lfts t, c)
      else
        let subs' = comp_subs lfts e in
        mkProd (n, to_constr lfts t, subst_constr (subs_lift subs') c)
    | FLetIn (n,b,t,f,e) ->
      let subs = comp_subs (el_lift lfts) (subs_lift e) in
        mkLetIn (n, to_constr lfts b,
                    to_constr lfts t,
                    subst_constr subs f)
    | FEvar ((ev,args),env) ->
      let subs = comp_subs lfts env in
        mkEvar(ev,Array.map (fun a -> subst_constr subs a) args)

and subst_constr subst c = match [@ocaml.warning "-4"] Constr.kind c with
| Rel i ->
  begin match expand_rel i subst with
  | Inl (k, lazy v) -> Vars.lift k v
  | Inr (m, _) -> mkRel m
  end
| _ ->
  Constr.map_with_binders Esubst.subs_lift subst_constr subst c

and comp_subs el s =
  Esubst.lift_subst (fun el c -> lazy (to_constr el c)) el s

(* This function defines the correspondance between constr and
   fconstr. When we find a closure whose substitution is the identity,
   then we directly return the constr to avoid possibly huge
   reallocation. *)
let term_of_fconstr c = to_constr el_id c

(* fstrong applies unfreeze_fun recursively on the (freeze) term and
 * yields a term.  Assumes that the unfreeze_fun never returns a
 * FCLOS term.
let rec fstrong unfreeze_fun lfts v =
  to_constr (fstrong unfreeze_fun) lfts (unfreeze_fun v)
*)

(*let rec zip m stk =
  match stk with
    | [] -> m
    | Zapp args :: s -> zip {norm=neutr m.norm; term=FApp(m, args)} s
    | ZcaseT(ci,p,br,e)::s ->
        let t = FCaseT(ci, p, m, br, e) in
        zip {norm=neutr m.norm; term=t} s
    | Zproj p :: s ->
        zip {norm=neutr m.norm; term=FProj(Projection.make p true,m)} s
    | Zfix(fx, e, par)::s ->
        zip fx (par @ append_stack [|m|] s)
    | Zshift(n)::s ->
        zip (lift_fconstr n m) s
        *)

(*********************************************************************)

(* The assertions in the functions below are granted because they are
   called only when m is a constructor, a cofix
   (strip_update_shift_app), a fix (get_nth_arg) or an abstraction
   (strip_update_shift, through get_arg). *)

(* optimised for the case where there are no shifts... *)
let strip_update_shift_app stk =
  let rec strip_rec rstk depth = function
    | Zshift(k) as e :: s ->
        strip_rec (e::rstk) (depth+k) s
    | (Zapp args :: s) ->
        strip_rec (Zapp args :: rstk) depth s
    | ((ZcaseT _ | Zproj _ | Zfix _) :: _ | []) as stk ->
      (depth,List.rev rstk, stk)
  in
  strip_rec [] 0 stk

let get_nth_arg n stk =
  let rec strip_rec rstk n = function
    | Zshift _ as e :: s ->
        strip_rec (e::rstk) n s
    | Zapp args::s' ->
        let q = Array.length args in
        if n >= q
        then
          strip_rec (Zapp args::rstk) (n-q) s'
        else
          let bef = Array.sub args 0 n in
          let aft = Array.sub args (n+1) (q-n-1) in
          let stk' =
            List.rev (if Int.equal n 0 then rstk else (Zapp bef :: rstk)) in
          (Some (stk', args.(n), append_stack aft s'))
    | ((ZcaseT _ | Zproj _ | Zfix _) :: _ | []) -> None in
  strip_rec [] n stk

(* Beta reduction: look for an applied argument in the stack.
   Since the encountered update marks are removed, h must be a whnf *)
let rec get_args n tys f e = function
    | Zshift k :: s ->
        get_args n tys f (subs_shft (k,e)) s
    | Zapp l :: s ->
        let na = Array.length l in
        if n == na then (Inl (subs_cons(l,e)),s)
        else if n < na then (* more arguments *)
          let args = Array.sub l 0 n in
          let eargs = Array.sub l n (na-n) in
          (Inl (subs_cons(args,e)), Zapp eargs :: s)
        else (* more lambdas *)
          let etys = List.skipn na tys in
          get_args (n-na) etys f (subs_cons(l,e)) s
    | ((ZcaseT _ | Zproj _ | Zfix _) :: _ | []) as stk ->
      (Inr (FLambda(n,tys,f,e)), stk)

(* Eta expansion: add a reference to implicit surrounding lambda at end of stack *)
let eta_expand_stack stk =
  stk @ [Zshift 1; Zapp [| { term = FEVAL (FRel 1, [], Norm) } |]]

(* Iota reduction: extract the arguments to be passed to the Case
   branches *)
let rec reloc_rargs_rec depth = function
  | Zapp args :: s ->
    Zapp (lift_fconstr_vect depth args) :: reloc_rargs_rec depth s
  | Zshift(k)::s -> if Int.equal k depth then s else reloc_rargs_rec (depth-k) s
  | ((ZcaseT _ | Zproj _ | Zfix _) :: _ | []) as stk -> stk

let reloc_rargs depth stk =
  if Int.equal depth 0 then stk else reloc_rargs_rec depth stk

let rec try_drop_parameters depth n = function
    | Zapp args::s ->
        let q = Array.length args in
        if n > q then try_drop_parameters depth (n-q) s
        else if Int.equal n q then reloc_rargs depth s
        else
          let aft = Array.sub args n (q-n) in
          reloc_rargs depth (append_stack aft s)
    | Zshift(k)::s -> try_drop_parameters (depth-k) n s
    | [] ->
        if Int.equal n 0 then []
        else raise Not_found
    | (ZcaseT _ | Zproj _ | Zfix _) :: _ -> assert false
        (* strip_update_shift_app only produces Zapp and Zshift items *)

let drop_parameters depth n argstk =
  try try_drop_parameters depth n argstk
  with Not_found ->
  (* we know that n < stack_args_size(argstk) (if well-typed term) *)
  anomaly (Pp.str "ill-typed term: found a match on a partially applied constructor.")

(** [eta_expand_ind_stack env ind c s t] computes stacks corresponding
    to the conversion of the eta expansion of t, considered as an inhabitant
    of ind, and the Constructor c of this inductive type applied to arguments
    s.
    @assumes [t] is an irreducible term, and not a constructor. [ind] is the inductive
    of the constructor term [c]
    @raise Not_found if the inductive is not a primitive record, or if the
    constructor is partially applied.
 *)
let eta_expand_ind_stack env ind s (f, s') =
  let open Declarations in
  let mib = lookup_mind (fst ind) env in
  (* disallow eta-exp for non-primitive records *)
  if not (mib.mind_finite == BiFinite) then raise Not_found;
  match Declareops.inductive_make_projections ind mib with
  | Some projs ->
    (* (Construct, pars1 .. parsm :: arg1...argn :: []) ~= (f, s') ->
           arg1..argn ~= (proj1 t...projn t) where t = zip (f,s') *)
    let pars = mib.Declarations.mind_nparams in
    let right = match f.term with
    | FEVAL (m, stk, _) -> { term = FEVAL (m, stk @ s', Red) }
    | FLOCK | FCLOS _ | FLIFT _ -> assert false
    in
    let (depth, args, _s) = strip_update_shift_app s in
    (** Try to drop the params, might fail on partially applied constructors. *)
    let argss = try_drop_parameters depth pars args in
    let map p = { term = FEVAL (FProj (Projection.make p true, right), [], Red) } in
    let hstack = Array.map map projs in
    argss, [Zapp hstack]
  | None -> raise Not_found (* disallow eta-exp for non-primitive records *)

let rec project_nth_arg n = function
  | Zapp args :: s ->
      let q = Array.length args in
        if n >= q then project_nth_arg (n - q) s
        else (* n < q *) args.(n)
  | (ZcaseT _ | Zproj _ | Zfix _ | Zshift _) :: _ | [] -> assert false
      (* After drop_parameters we have a purely applicative stack *)


(* Iota reduction: expansion of a fixpoint.
 * Given a fixpoint and a substitution, returns the corresponding
 * fixpoint body, and the substitution in which it should be
 * evaluated: its first variables are the fixpoint bodies
 *
 * FCLOS(fix Fi {F0 := T0 .. Fn-1 := Tn-1}, S)
 *    -> (S. FCLOS(F0,S) . ... . FCLOS(Fn-1,S), Ti)
 *)
(* does not deal with FLIFT *)
let contract_fix_vect fix env  =
  let ((reci,i),(_,_,bds as rdcl)) = fix in
  let make_body j = { term = FEVAL (FFix (((reci,j),rdcl),env), [], Cstr) } in
  let nfix = Array.length bds in
  (subs_cons(Array.init nfix make_body, env), bds.(i))

let contract_cofix_vect cofix env =
  let (i,(_,_,bds as rdcl)) = cofix in
  let make_body j = { term = FEVAL (FCoFix ((j,rdcl),env), [], Cstr) } in
  let nfix = Array.length bds in
  (subs_cons(Array.init nfix make_body, env), bds.(i))

let unfold_projection info p =
  if red_projection info.i_flags p
  then
    Some (Zproj (Projection.repr p))
  else None

(*********************************************************************)
(* A machine that inspects the head of a term until it finds an
   atom or a subterm that may produce a redex (abstraction,
   constructor, cofix, letin, constant), or a neutral term (product,
   inductive) *)
(************************************************************************)

let rec knh info tab m stk =
  match m.term with
  | FCLOS (t, e) ->
    let () = m.term <- FLOCK in
    let (f, stk', n) = knht info tab e t [] in
    let () = m.term <- FEVAL (f, stk', n) in
    knhc info tab f (stk' @ stk)
  | FEVAL (m, stk', _) ->
    knhc info tab m (stk' @ stk)
  | FLIFT (f, k) ->
    let () = m.term <- FLOCK in
    let (f, stk', flg) = knh info tab f [] in
    let stk' = stk' @ [Zshift k] in
    let () = m.term <- FEVAL (f, stk', flg) in
    knhc info tab f (stk' @ stk)
  | FLOCK ->
    (** Cannot happen, this would mean there is a cycle in the lazy cells *)
    assert false

and knhc info tab m stk = match m with
  | FRel _ | FEvar _ | FAtom _ | FInd _ | FProd _ ->
    (m, stk, Whnf)
  | FFlex(ConstKey (kn,_ as c)) when red_set info.i_flags (fCONST kn) ->
      (match ref_value_cache info tab (ConstKey c) with
          Some v -> knh info tab v stk
        | None -> (m, stk, Norm))
  | FFlex(VarKey id) when red_set info.i_flags (fVAR id) ->
      (match ref_value_cache info tab (VarKey id) with
          Some v -> knh info tab v stk
        | None -> (m, stk, Norm))
  | FFlex(RelKey k) when red_set info.i_flags fDELTA ->
      (match ref_value_cache info tab (RelKey k) with
          Some v -> knh info tab v stk
        | None -> (m,stk, Norm))
  | FLetIn (_,v,_,bd,e) when red_set info.i_flags fZETA ->
      knht info tab (subs_cons([|v|],e)) bd stk
  | FFix ((ri, n), (_, _, _) as fx, e) ->
    begin match get_nth_arg ri.(n) stk with
    | Some (pars, arg, stk') -> knh info tab arg (Zfix(fx, e, pars)::stk')
    | None -> (FFix (fx, e), stk, Cstr)
    end
  | FProj (p, c) ->
    begin match unfold_projection info p with
    | None -> (m, stk, Red)
    | Some s -> knh info tab c (s :: stk)
    end
  | FConstruct((_ind,c),_u) ->
     let use_match = red_set info.i_flags fMATCH in
     let use_fix = red_set info.i_flags fFIX in
     if use_match || use_fix then
      (match [@ocaml.warning "-4"] strip_update_shift_app stk with
        | (depth, args, ZcaseT(ci,_,br,e)::s) when use_match ->
            assert (ci.ci_npar>=0);
            let rargs = drop_parameters depth ci.ci_npar args in
            knht info tab e br.(c-1) (rargs@s)
        | (_, cargs, Zfix(fx, e, par)::s) when use_fix ->
            let rarg = { term = FEVAL (m, cargs, Cstr) } in
            let stk' = par @ append_stack [|rarg|] s in
            let (fxe,fxbd) = contract_fix_vect fx e in
            knht info tab fxe fxbd stk'
        | (depth, args, Zproj p::s) when use_match ->
            let rargs = drop_parameters depth (Projection.Repr.npars p) args in
            let rarg = project_nth_arg (Projection.Repr.arg p) rargs in
            knh info tab rarg s
        | (_,args,s) -> (m,args@s,Cstr))
     else (m,stk,Cstr)
  | FLambda(n,tys,f,e) when red_set info.i_flags fBETA ->
      (match get_args n tys f e stk with
          Inl e', s -> knht info tab e' f s
        | Inr lam, s -> (lam, s, Cstr))
  | FCoFix (cfx, e) when red_set info.i_flags fCOFIX ->
      (match strip_update_shift_app stk with
        | (_, args, (((ZcaseT _|Zproj _)::_) as stk')) ->
            let (fxe,fxbd) = contract_cofix_vect cfx e in
            knht info tab fxe fxbd (args@stk')
        | (_,args, ((Zapp _ | Zfix _ | Zshift _) :: _ | [] as s)) -> (m,args@s,Cstr))
  | FCoFix _ | FLambda _ | FFlex (RelKey _ | VarKey _ | ConstKey _) | FLetIn _ ->
    (m, stk, Red)

(* The same for pure terms *)
and knht info tab e t stk =
  match kind t with
    | Ind ind -> (FInd ind, stk, Whnf)
    | Prod (n, t, c) -> (FProd (n, mk_clos e t, c, e), stk, Whnf)
    | Meta _ | Sort _ -> (FAtom t, stk, Whnf)
    | App(a,b) ->
        knht info tab e a (append_stack (mk_clos_vect e b) stk)
    | Case(ci,p,t,br) ->
        knht info tab e t (ZcaseT(ci, p, br, e)::stk)
    | Fix fx ->
      knhc info tab (FFix (fx, e)) stk
    | Cast(a,_,_) -> knht info tab e a stk
    | Rel n -> knh info tab (clos_rel e n) stk
    | Proj (p, c) ->
      knhc info tab (FProj (p, mk_clos e c)) stk
    | CoFix cfx ->
      knhc info tab (FCoFix (cfx, e)) stk
    | Lambda _ ->
      knhc info tab (mk_lambda e t) stk
    | LetIn (n,b,t,c) ->
      knhc info tab (FLetIn (n, mk_clos e b, mk_clos e t, c, e)) stk
    | Evar ev ->
      begin match info.i_cache.i_sigma ev with
      | Some c -> knht info tab e c stk
      | None -> (FEvar (ev, e), stk, Whnf)
      end
    | Const c -> knhc info tab (FFlex (ConstKey c)) stk
    | Construct c -> knhc info tab (FConstruct c) stk
    | Var id -> knhc info tab (FFlex (VarKey id)) stk

(************************************************************************)

(* Initialization and then normalization *)

let whd_stack info tab m stk =
  let (m, stk, flg) = knh info tab m stk in
  ({ term = FEVAL (m, [], flg) }, stk)

let create_clos_infos ?(evars=fun _ -> None) flgs env =
  let share = (Environ.typing_flags env).Declarations.share_reduction in
  let cache = {
    i_env = env;
    i_sigma = evars;
    i_share = share;
  } in
  { i_flags = flgs; i_cache = cache }

let create_tab () = KeyTable.create 17

let oracle_of_infos infos = Environ.oracle infos.i_cache.i_env

let infos_with_reds infos reds =
  { infos with i_flags = reds }

let unfold_reference info tab key =
  match key with
  | ConstKey (kn,_) ->
    if red_set info.i_flags (fCONST kn) then
      ref_value_cache info tab key
    else None
  | VarKey i ->
    if red_set info.i_flags (fVAR i) then
      ref_value_cache info tab key
    else None
  | RelKey _ -> ref_value_cache info tab key
