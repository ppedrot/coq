(* #!/usr/bin/ocaml *)

module Int =
struct
  type t = int
  let compare (x : int) (y : int) = Pervasives.compare x y
end

module IntPair =
struct
  type t = int * int
  let compare (p : t) (q : t) =
    let c = Pervasives.compare (fst p) (fst q) in
    if c = 0 then Pervasives.compare (snd p) (snd q)
    else c
end

module IntMap = Map.Make(Int)
module IntSet = Set.Make(Int)

module IntPairMap = Map.Make(IntPair)
module IntPairSet = Set.Make(IntPair)

let add_map p s =
  let n = try IntPairMap.find p s with Not_found -> 0 in
  IntPairMap.add p (succ n) s

let split_line s =
  let i = ref 0 in
  let break = ref true in
  let len = String.length s in
  while !break && !i < len do
    if s.[!i] == ',' then break := false
    else incr i
  done;
  let () = if !i == len then raise Exit in
  let p = String.sub s 0 !i in
  let q = String.sub s (!i + 1) (len - !i - 1) in
  (int_of_string p, int_of_string q)

let rec read_lines accu chan =
  let line = try Some (input_line chan) with End_of_file -> None in
  match line with
  | None -> accu
  | Some line ->
    let accu = try add_map (split_line line) accu with _ -> accu in
    read_lines accu chan

let read_lines file =
  let chan = open_in file in
  let lines = read_lines IntPairMap.empty chan in
  let () = close_in chan in
  lines

let get_nodes edges =
  let fold (p, q) _ accu = IntSet.add p (IntSet.add q accu) in
  IntPairMap.fold fold edges IntSet.empty

let print_nodes chan nodes =
  let iter n = Printf.fprintf chan "inf line*0x%x\n" n in
  IntSet.iter iter nodes

let rec read_locations accu chan =
  let line = try Some (input_line chan) with End_of_file -> None in
  match line with
  | None -> accu
  | Some line -> read_locations (line :: accu) chan

let get_location exe nodes =
  let src = Filename.temp_file "decode" "" in
  let dst = Filename.temp_file "decode" "" in
  let chan = open_out src in
  let () = print_nodes chan nodes in
  let () = close_out chan in
  let cmd = "gdb " ^ exe ^ " --batch -x " ^ src ^ " | sed 's/\" starts.*//' | \
  sed 's/\"//' | sed 's/No line number information available for address //' | \
  sed 's/Line \\([0-9]*\\) of \\(.*\\)/\\2:\\1/' | sed 's/^/\"/' | \
  sed 's/$/\"/' | sed 's/ /_/g' > " ^ dst
  in
  let _ = Sys.command cmd in
  let chan = open_in dst in
  let locs = List.rev (read_locations [] chan) in
  let () = close_in chan in
  let () = Sys.remove src in
  let () = Sys.remove dst in
  let fold node (rem, accu) = match rem with
  | [] -> assert false
  | loc :: rem -> (rem, IntMap.add node loc accu)
  in
  let _, map = IntSet.fold fold nodes (locs, IntMap.empty) in
  map

let print_graph edges locs =
  let iter ((src, dst), n) =
    let src = IntMap.find src locs in
    let dst = IntMap.find dst locs in
    let rng = 1. +. log (float_of_int n) in
    Printf.printf "%s -> %s [label=%i,penwidth=%f]\n" src dst n rng
  in
  let values = IntPairMap.bindings edges in
  let values = List.sort (fun (_, n) (_, m) -> Int.compare n m) values in
  List.iter iter values

let () =
  let edges = Sys.argv.(1) in
  let exe = Sys.argv.(2) in
  let () = Printf.eprintf "Reading edges...\n%!" in
  let edges = read_lines edges in
  let nodes = get_nodes edges in
  let () = Printf.eprintf "Getting locations...\n%!" in
  let locs = get_location exe nodes in
  let () = Printf.eprintf "Printing graph...\n%!" in
  print_graph edges locs
