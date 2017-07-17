(* #!/usr/bin/env ocaml *)

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

#use "topfind";;
#require "unix";;

(** Global variables *)

let ocamlobjinfo = "ocamlobjinfo"

let coq_directories = [
  "kernel";
  "engine";
  "interp";
  "intf";
  "kernel";
  "lib";
  "library";
  "parsing";
  "pretyping";
  "proofs";
  "stm";
  "tactics";
  "toplevel";
  "vernac";
]

(** Boilerplate *)

let error msg =
  Printf.eprintf "%s\n%!" msg; exit 1

let split c s =
  let len = String.length s in
  let rec split n =
    try
      let pos = String.index_from s n c in
      let dir = String.sub s n (pos-n) in
      dir :: split (succ pos)
    with
      | Not_found -> [String.sub s n (len-n)]
  in
  if len = 0 then [] else split 0

let rec input_lines accu chan =
  let line = try Some (input_line chan) with End_of_file -> None in
  match line with
  | None -> List.rev accu
  | Some l -> input_lines (l :: accu) chan

let read_file f =
  let chan = open_in f in
  let lines = input_lines [] chan in
  let () = close_in chan in
  lines

let read_command cmd =
  let chan = Unix.open_process_in cmd in
  let lines = input_lines [] chan in
  let _ = Unix.close_process_in chan in
  lines

(** Datatypes *)

type cmx = {
  cmx_crc : string;
  cmx_name : string;
  cmx_intf : (string * string) list;
  cmx_impl : (string * string) list;
}

type cmi = {
  cmi_crc : string;
  cmi_name : string;
  cmi_intf : (string * string) list;
}

(*let get_mllib path =
  try
    let files = Array.to_list (Sys.readdir path) in
    let mllib = List.find (fun s -> Filename.check_suffix s "mllib") files in
    let files = read_file (Filename.concat path mllib) in
    List.map (fun f -> path, f) files
  with _ ->
    error (Printf.sprintf "No mllib found in %s" path)

let get_from_mllib path name extension =
  (** Name is capitalized from the mllib *)
  let f1 = Filename.concat path (name ^ extension) in
  let f2 = Filename.concat path (String.uncapitalize_ascii name ^ extension) in
  if Sys.file_exists f1 then f1
  else if Sys.file_exists f2 then f2
  else
    error (Printf.sprintf "Missing unit %s with extension %s in %s" name extension path)*)

let get_all_files path ext =
  let dir = Sys.readdir path in
  let dir = Array.to_list dir in
  let files = List.filter (fun s -> Filename.check_suffix s ext) dir in
  List.map (fun s -> Filename.concat path s) files

(** Ad-hoc parsing of ocamlobjinfo output *)

exception ParseError

let is_hexa = function
| 'a'..'f' -> true
| '0'..'9' -> true
| _ -> false

let is_ident = function
| '_' -> true
| 'a'..'z' -> true
| 'A'..'Z' -> true
| '0'..'9' -> true
| _ -> false

let is_exactly s s' =
  if String.equal s s' then () else raise ParseError

let rec junk_until check = function
| [] -> raise ParseError
| hd :: lines ->
  let ans = try Some (check hd) with ParseError -> None in
  match ans with
  | None -> junk_until check lines
  | Some hd -> (hd, lines)

let accumulate_while check lines =
  let rec aux accu = function
  | [] -> List.rev accu, []
  | hd :: lines ->
    let ans = try Some (check hd) with ParseError -> None in
    match ans with
    | None -> List.rev accu, hd :: lines
    | Some hd -> aux (hd :: accu) lines
  in
  aux [] lines

let parse_unit s =
  if String.length s < 35 then raise ParseError;
  if s.[0] != '\t' then raise ParseError;
  for i = 1 to 32 do
    if not (is_hexa s.[i]) then raise ParseError;
  done;
  if s.[33] != '\t' then raise ParseError;
  for i = 34 to String.length s - 1 do
    if not (is_ident s.[i]) then raise ParseError;
  done;
  let digest = String.sub s 1 32 in
  let name = String.sub s 34 (String.length s - 34) in
  (digest, name)

let parse_cmx_name line = match split ' ' line with
| ["Name:"; s] ->
  for i = 0 to String.length s - 1 do
    if not (is_ident s.[i]) then raise ParseError;
  done;
  s
| _ -> raise ParseError

let parse_cmx_crc line = match split ' ' line with
| ["CRC"; "of"; "implementation:"; s] ->
  for i = 0 to 31 do
    if not (is_hexa s.[i]) then raise ParseError;
  done;
  s
| _ -> raise ParseError

let parse_cmi_name line = match split ' ' line with
| ["Unit"; "name:"; s] ->
  for i = 0 to String.length s - 1 do
    if not (is_ident s.[i]) then raise ParseError;
  done;
  s
| _ -> raise ParseError

let parse_cmx lines =
  let (name, lines) = junk_until parse_cmx_name lines in
  let (crc, lines) = junk_until parse_cmx_crc lines in
  let ((), lines) = junk_until (is_exactly "Interfaces imported:") lines in
  let (intf, lines) = accumulate_while parse_unit lines in
  let ((), lines) = junk_until (is_exactly "Implementations imported:") lines in
  let (impl, _) = accumulate_while parse_unit lines in
  { cmx_name = name;
    cmx_crc = crc;
    cmx_impl = impl;
    cmx_intf = intf; }

let parse_cmi lines =
  let (name, lines) = junk_until parse_cmi_name lines in
  let ((), lines) = junk_until (is_exactly "Interfaces imported:") lines in
  let (intf, _) = accumulate_while parse_unit lines in
  let crc, intf = match intf with
  | [] -> raise ParseError
  | (crc, name') :: intf ->
    assert (String.equal name name');
    crc, intf
  in
  { cmi_name = name;
    cmi_crc = crc;
    cmi_intf = intf; }

let read_cmx f =
  try
    parse_cmx (read_command (Printf.sprintf "%s %s" ocamlobjinfo f))
  with e ->
    error (Printf.sprintf "Cannot parse file %s" f)

let read_cmi f =
  try
    parse_cmi (read_command (Printf.sprintf "%s %s" ocamlobjinfo f))
  with e ->
    error (Printf.sprintf "Cannot parse file %s" f)

(** Graph computation *)

module StringMap = Map.Make(String)

type node_crc =
| ImplOnly of string
| IntfOnly of string
| BothCrc of string * string

type node = {
  intf : string list;
  impl : string list
}

let empty_node = { intf = []; impl = [] }

type graph = {
  data : node_crc StringMap.t;
  node : node StringMap.t;
}

let add_intf g (digest, name) =
  let crc = try Some (StringMap.find name g.data) with Not_found -> None in
  match crc with
  | None ->
    { g with data = StringMap.add name (IntfOnly digest) g.data } 
  | Some (ImplOnly d') ->
    { g with data = StringMap.add name (BothCrc (digest, d')) g.data }
  | Some (IntfOnly d' | BothCrc (d', _)) ->
    if String.equal d' digest then g
    else error (Printf.sprintf "CRC disagree on interface %s" name)

let add_impl g (digest, name) =
  let crc = try Some (StringMap.find name g.data) with Not_found -> None in
  match crc with
  | None ->
    { g with data = StringMap.add name (ImplOnly digest) g.data }
  | Some (IntfOnly d') ->
    { g with data = StringMap.add name (BothCrc (d', digest)) g.data }
  | Some (ImplOnly d' | BothCrc (_, d')) ->
    if String.equal d' digest then g
    else error (Printf.sprintf "CRC disagree on implementation %s" name)

let empty_graph = { node = StringMap.empty; data = StringMap.empty }

let rec filter name accu = function
| [] -> accu
| (_, name') :: rem ->
  if String.equal name name' then
    (** Don't add trivial dependencies between interfaces and implementation *)
    filter name accu rem
  else
    filter name (name' :: accu) rem

let add_cmx g cmx =
  let g = List.fold_left add_intf g cmx.cmx_intf in
  let g = List.fold_left add_impl g cmx.cmx_impl in
  let name = cmx.cmx_name in
  let node = try StringMap.find name g.node with Not_found -> empty_node in
  let node = {
    impl = filter name node.impl cmx.cmx_impl;
    intf = filter name node.intf cmx.cmx_intf;
  } in
  { g with node = StringMap.add name node g.node }

let add_cmi g cmi =
  let g = List.fold_left add_intf g cmi.cmi_intf in
  let name = cmi.cmi_name in
  let node = try StringMap.find name g.node with Not_found -> empty_node in
  let node = {
    impl = node.impl;
    intf = filter name node.intf cmi.cmi_intf;
  } in
  { g with node = StringMap.add name node g.node }

type answer =
| Cycle of (bool * string) list (** True if implementation *)
| DAG of bool StringMap.t

let rec search g name seen =
  let visited = try Some (StringMap.find name seen) with Not_found -> None in
  match visited with
  | None ->
    let seen = StringMap.add name true seen in
    let node = try StringMap.find name g.node with Not_found -> empty_node in
    let next =
      List.map (fun n -> (true, n)) node.impl @
      List.map (fun n -> (false, n)) node.intf
    in
    begin match search_next g seen next with
    | Cycle _ as c -> c
    | DAG seen -> DAG (StringMap.add name false seen)
    end
  | Some true -> Cycle []
  | Some false -> DAG seen


and search_next g seen = function
| [] -> DAG seen
| (impl, node) :: rem ->
  match search g node seen with
  | Cycle stack -> Cycle ((impl, node) :: stack)
  | DAG seen -> search_next g seen rem

let rec search_all g = function
| [] -> None
| (name, _) :: rem ->
  match search g name StringMap.empty with
  | Cycle c -> Some (name, c)
  | DAG _ -> search_all g rem


(** Init checks *)

let () =
  if Sys.command ocamlobjinfo == 127 then error "Missing program 'ocamlobjinfo'"

(** Run *)

let () =
  let () = Printf.printf "Reading the directory...\n%!" in
  let get_all_in_coq ext =
    let files = List.map (fun path -> get_all_files path ext) coq_directories in
    List.concat files
  in
  let cmx = get_all_in_coq ".cmx" in
  let cmi = get_all_in_coq ".cmi" in
  let () = Printf.printf "Parsing object files...\n%!" in
  let cmx = List.map read_cmx cmx in
  let cmi = List.map read_cmi cmi in
  let () = Printf.printf "Computing the graph...\n%!" in
  let g = empty_graph in
  let g = List.fold_left add_cmx g cmx in
  let g = List.fold_left add_cmi g cmi in
  let () = Printf.printf "Looking for cycles...\n%!" in
  match search_all g (StringMap.bindings g.node) with
  | None -> ()
  | Some (name, c) ->
    let iter (impl, s) =
      let t = if impl then "impl" else "intf" in
      Printf.printf "%s -> %s\n%!" t s
    in
    Printf.printf "Found a cycle!\n%!";
    Printf.printf "From %s\n%!" name;
    List.iter iter c

