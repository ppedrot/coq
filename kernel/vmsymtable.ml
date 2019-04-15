(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Bruno Barras for Benjamin Grégoire as part of the
   bytecode-based reduction machine, Oct 2004 *)
(* Bug fix #1419 by Jean-Marc Notin, Mar 2007 *)

(* This file manages the table of global symbols for the bytecode machine *)

open Util
open Names
open Vmvalues
open Vmemitcodes
open Vmbytecodes
open Declarations
open Environ
open Vmbytegen

module NamedDecl = Context.Named.Declaration
module RelDecl = Context.Rel.Declaration

type vm_global = values array

(* interpreteur *)
external coq_interprete : tcode -> values -> atom array -> vm_global -> Vmvalues.vm_env -> int -> values =
  "coq_interprete_byte" "coq_interprete_ml"

(* table pour les structured_constant et les annotations des switchs *)

module HashMap (M : Hashtbl.HashedType) :
sig
  type +'a t
  val empty : 'a t
  val add : M.t -> 'a -> 'a t -> 'a t
  val find : M.t -> 'a t -> 'a
end =
struct
  type 'a t = (M.t * 'a) list Int.Map.t
  let empty = Int.Map.empty
  let add k v m =
    let hash = M.hash k in
    try Int.Map.modify hash (fun _ l -> (k, v) :: l) m
    with Not_found -> Int.Map.add hash [k, v] m
  let find k m =
    let hash = M.hash k in
    let l = Int.Map.find hash m in
    List.assoc_f M.equal k l
end

module SConstTable = HashMap (struct
  type t = structured_constant
  let equal = eq_structured_constant
  let hash = hash_structured_constant
end)

module AnnotTable = HashMap (struct
  type t = annot_switch
  let equal = eq_annot_switch
  let hash = hash_annot_switch
end)

module ProjNameTable = HashMap (Projection.Repr.CanOrd)

module GlobVal :
sig
  type key = int
  type t
  val empty : int -> t
  val push : t -> values -> key * t
  val vm_global : t -> vm_global
  (** Warning: due to sharing, the resulting value can be modified by
      persistent operations. When calling this function one must ensure
      that no other context modification is performed before the value drops
      out of scope. *)
end =
struct
  type key = int

  type view =
  | Root of values array
  | DSet of int * values * view ref

  type t = {
    data : view ref;
    size : int;
    (** number of actual elements in the array *)
  }

  let empty n = {
    data = ref (Root (Array.make n crazy_val));
    size = 0;
  }

  let rec rerootk t k = match !t with
  | Root _ -> k ()
  | DSet (i, v, t') ->
    let next () = match !t' with
    | Root a as n ->
      let v' = Array.unsafe_get a i in
      let () = Array.unsafe_set a i v in
      let () = t := n in
      let () = t' := DSet (i, v', t) in
      k ()
    | DSet _ -> assert false
    in
    rerootk t' next

  let reroot t = rerootk t (fun () -> ())

  let push { data = t; size = i } v =
    let () = reroot t in
    match !t with
    | DSet _ -> assert false
    | Root a as n ->
      let len = Array.length a in
      let data =
        if i < len then
          let old = Array.unsafe_get a i in
          if old == v then t
          else
            let () = Array.unsafe_set a i v in
            let res = ref n in
            let () = t := DSet (i, old, res) in
            res
        else
          let nlen = 2 * len + 1 in
          let nlen = min nlen Sys.max_array_length in
          let () = assert (i < nlen) in
          let a' = Array.make nlen crazy_val in
          let () = Array.blit a 0 a' 0 len in
          let () = Array.unsafe_set a' i v in
          let res = ref (Root a') in
          let () = t := DSet (i, crazy_val, res) in
          res
      in
      (i, { data; size = i + 1 })

  let vm_global { data; _ } =
    let () = reroot data in
    match !data with
    | DSet _ -> assert false
    | Root a -> (a : vm_global)

end


(*******************)
(* Linkage du code *)
(*******************)

(* Table des globaux *)

(** [global_table] containts values of global constants, switch annotations,
    structure_constant and projections. *)

type global_table = {
  glob_val : GlobVal.t;
  glob_sconst : GlobVal.key SConstTable.t;
  glob_annot : GlobVal.key AnnotTable.t;
  glob_projname : GlobVal.key ProjNameTable.t;
}

let get_global_data table = GlobVal.vm_global table.glob_val

let set_global v table =
  let (n, glob_val) = GlobVal.push table.glob_val v in
  let table = { table with glob_val } in
  table, n

(* Initialization of OCaml primitives *)
let parray_make = set_global Vmvalues.parray_make
let parray_get = set_global Vmvalues.parray_get
let parray_get_default = set_global Vmvalues.parray_get_default
let parray_set = set_global Vmvalues.parray_set
let parray_copy = set_global Vmvalues.parray_copy
let parray_length = set_global Vmvalues.parray_length

(*************************************************************)
(*** Mise a jour des valeurs des variables et des constantes *)
(*************************************************************)

exception NotEvaluated

let key rk =
  match !rk with
  | None -> raise NotEvaluated
  | Some k ->
      try CEphemeron.get k
      with CEphemeron.InvalidKey -> raise NotEvaluated

(************************)
(* traduction des patch *)

(* slot_for_*, calcul la valeur de l'objet, la place
   dans la table global, rend sa position dans la table *)

let slot_for_str_cst key table =
  try table, SConstTable.find key table.glob_sconst
  with Not_found ->
    let table, n = set_global (val_of_str_const key) table in
    let glob_sconst = SConstTable.add key n table.glob_sconst in
    let table = { table with glob_sconst } in
    table, n

let slot_for_annot key table =
  try table, AnnotTable.find key table.glob_annot
  with Not_found ->
    let table, n = set_global (val_of_annot_switch key) table in
    let glob_annot = AnnotTable.add key n table.glob_annot in
    let table = { table with glob_annot } in
    table, n

let slot_for_caml_prim =
  let open CPrimitives in function
  | Arraymake -> parray_make
  | Arrayget -> parray_get
  | Arraydefault -> parray_get_default
  | Arrayset -> parray_set
  | Arraycopy -> parray_copy
  | Arraylength -> parray_length
  | _ -> assert false

let slot_for_proj_name key table =
  try table, ProjNameTable.find key table.glob_projname
  with Not_found ->
    let table, n = set_global (val_of_proj_name key) table in
    let glob_projname = ProjNameTable.add key n table.glob_projname in
    let table = { table with glob_projname } in
    table, n

let rec slot_for_getglobal env sigma kn table =
  let (cb,(_,rk)) = lookup_constant_key kn env in
  try table, key rk
  with NotEvaluated ->
(*    Pp.msgnl(str"not yet evaluated");*)
    let table, pos =
      match cb.const_body_code with
      | None -> set_global (val_of_constant kn) table
      | Some code ->
        match code with
        | BCdefined (code, fv) ->
           let table, v = eval_to_patch env sigma (code, fv) table in
           set_global v table
        | BCalias kn' -> slot_for_getglobal env sigma kn' table
        | BCconstant -> set_global (val_of_constant kn) table
    in
(*Pp.msgnl(str"value stored at: "++int pos);*)
    rk := Some (CEphemeron.create pos);
    table, pos

and slot_for_fv env sigma fv table =
  let fill_fv_cache cache id v_of_id env_of_id b =
    let table, v, d =
      match b with
      | None -> table, v_of_id id, Id.Set.empty
      | Some c ->
        let table, v = val_of_constr (env_of_id id env) sigma c table in
        table, v, Environ.global_vars_set env c
    in
    build_lazy_val cache (v, d); table, v in
  let val_of_rel i = val_of_rel (nb_rel env - i) in
  let idfun _ x = x in
  match fv with
  | FVnamed id ->
      let nv = lookup_named_val id env in
      begin match force_lazy_val nv with
      | None ->
         env |> lookup_named id |> NamedDecl.get_value |> fill_fv_cache nv id val_of_named idfun
      | Some (v, _) -> table, v
      end
  | FVrel i ->
      let rv = lookup_rel_val i env in
      begin match force_lazy_val rv with
      | None ->
        env |> lookup_rel i |> RelDecl.get_value |> fill_fv_cache rv i val_of_rel env_of_rel
      | Some (v, _) -> table, v
      end
  | FVevar evk -> table, val_of_evar evk
  | FVuniv_var _idu ->
    assert false

and eval_to_patch env sigma (code, fv) table =
  let slots = function
    | Reloc_annot a -> slot_for_annot a
    | Reloc_const sc -> slot_for_str_cst sc
    | Reloc_getglobal kn -> slot_for_getglobal env sigma kn
    | Reloc_proj_name p -> slot_for_proj_name p
    | Reloc_caml_prim op -> slot_for_caml_prim op
  in
  let table, tc = patch code slots table in
  let table, vm_env =
    (* Environment should look like a closure, so free variables start at slot 2. *)
    let a = Array.make (Array.length fv + 2) crazy_val in
    a.(1) <- Obj.magic 2;
    let fold i accu fv =
      let accu, v = slot_for_fv env sigma fv accu in
      let () = a.(i + 2) <- v in
      accu
    in
    let table = Array.fold_left_i fold table fv in
    table, a
  in
  let global = get_global_data table in
  let v = coq_interprete tc crazy_val (get_atom_rel ()) global (inj_env vm_env) 0 in
  table, v

and val_of_constr env sigma c table =
  match compile ~fail_on_error:true env sigma c with
  | Some v -> eval_to_patch env sigma v table
  | None -> assert false

let global_table = ref {
  glob_val = GlobVal.empty 4096;
  glob_sconst = SConstTable.empty;
  glob_annot = AnnotTable.empty;
  glob_projname = ProjNameTable.empty;
}

let val_of_constr env sigma c =
  let table, v = val_of_constr env sigma c !global_table in
  let () = global_table := table in
  v

let vm_interp code v env k =
  coq_interprete code v (get_atom_rel ()) (get_global_data !global_table) env k
