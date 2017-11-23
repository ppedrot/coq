open Names
open Cbytecodes

type reloc_info =
  | Reloc_annot of annot_switch
  | Reloc_const of structured_constant
  | Reloc_getglobal of Constant.t

type patches
type emitcodes

val length : emitcodes -> int

val patch : emitcodes -> patches -> (reloc_info -> int) -> emitcodes

type to_patch = emitcodes * patches * fv

val subst_to_patch : Mod_subst.substitution -> to_patch -> to_patch

type body_code =
  | BCdefined of to_patch
  | BCalias of Constant.t
  | BCconstant


type to_patch_substituted

val from_val : body_code -> to_patch_substituted

val force : to_patch_substituted -> body_code

val subst_to_patch_subst : Mod_subst.substitution -> to_patch_substituted -> to_patch_substituted

val repr_body_code :
  to_patch_substituted -> Mod_subst.substitution list option * body_code

val to_memory : bytecodes * bytecodes * fv -> to_patch
               (** init code, fun code, fv *)
