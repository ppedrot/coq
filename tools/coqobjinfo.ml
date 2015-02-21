(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type segment = {
  name : string;
  mutable pos : int;
  mutable content : Obj.t;
  mutable digest : string;
}

type dyn = int * Obj.t

type libobj = string * dyn

type dirpath = string list

type vodigest =
| Dvo_or_vi of Digest.t
| Dvivo of Digest.t * Digest.t

type library = {
  lib_path : dirpath;
  lib_data : Obj.t;
  lib_objs : (libobj list * libobj list);
  lib_deps : (dirpath * vodigest) array;
  lib_imps : dirpath array;
}

let make_segment name = { name ; pos = 0; content = Obj.repr 0; digest = "" }

let print_dirpath s = String.concat "." (List.rev s)

let print_summary segments =
  Printf.printf "Summary:\n";
  for i = 0 to Array.length segments - 1 do
    let s = segments.(i) in
    Printf.printf "  %s: %i [%s]\n%!" s.name s.pos (Digest.to_hex s.digest);
  done

let print_library obj =
  let (obj : library) = Obj.obj obj in
  let name = print_dirpath obj.lib_path in
  let () = Printf.printf "Name: %s\n" name in
  let () = Printf.printf "Depends on:\n" in
  for i = 0 to Array.length obj.lib_deps - 1 do
    let (dp, digest) = obj.lib_deps.(i) in
    Printf.printf "  %s\n" (print_dirpath dp);
  done;
  let () = Printf.printf "Imports:\n" in
  for i = 0 to Array.length obj.lib_imps - 1 do
    let dp = obj.lib_imps.(i) in
    Printf.printf "  %s\n" (print_dirpath dp);
  done;
  let iter_objs (name, (tag, _)) = Printf.printf "  %s %i\n" name tag in
  let () = Printf.printf "Substitutive objects:\n" in
  let () = List.iter iter_objs (fst obj.lib_objs) in
  ()

let visit_vo f =
  let segments = [|
    make_segment "library";
    make_segment "univ constraints of opaque proofs";
    make_segment "discharging info";
    make_segment "STM tasks";
    make_segment "opaque proofs";
  |] in
  let ch = open_in_bin f in
  let () =
    try
      let _magic = input_binary_int ch in
      for i = 0 to Array.length segments - 1 do
        let pos = input_binary_int ch in
        segments.(i).pos <- pos_in ch;
        segments.(i).content <- input_value ch;
        seek_in ch pos;
        segments.(i).digest <- Digest.input ch;
      done;
    with e -> close_in ch; raise e
  in
  print_library segments.(0).content;
  print_summary segments;
  ()

let _ =
  for i = 1 to Array.length Sys.argv - 1 do
    let file = Sys.argv.(i) in
    Printf.printf "File %s\n" file;
    visit_vo file;
    flush stdout;
  done
