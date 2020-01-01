(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type proxy = {
  mutable valid : bool;
  filename : string;
}

type 'a t = {
  data : (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t;
  proxy : proxy CEphemeron.key;
  (* Ensures that the proxy stays alive, otherwise the array could become
     invalid under our feet. *)
}
(* Invariants:
  - if proxy is alive, then the data array is mmapped from a disk file
  - otherwise it is an in-memory array
*)

let finaliser (s : proxy) =
  if s.valid then
    let () = Sys.remove s.filename in
    s.valid <- false

let handle filename =
  let fd = Unix.openfile filename [Unix.O_RDONLY] 0o400 in
  let data = Unix.map_file fd Bigarray.Char Bigarray.C_layout false [|-1|] in
  Bigarray.array1_of_genarray data

let make (v : 'a) : 'a t =
  let file, chan = Filename.open_temp_file "coqopaque" "" in
  let () = Marshal.to_channel chan v [] in
  let () = close_out chan in
  let proxy = { filename = file; valid = true } in
  let () = Gc.finalise finaliser proxy in
  let proxy = CEphemeron.create proxy in
  let data = handle file in
  { data; proxy }

let get (s : 'a t) = match CEphemeron.get s.proxy with
| proxy ->
  (* Data on disk *)
  let ()  = assert proxy.valid in
  let chan = open_in proxy.filename in
  let v = Marshal.from_channel chan in
  let () = close_in chan in
  v
| exception CEphemeron.InvalidKey ->
  (* Data in memory *)
  let data = s.data in
  let len = Bigarray.Array1.dim data in
  (* TODO: do something more intelligent *)
  let s = Bytes.create len in
  let () =
    for i = 0 to len - 1 do
      Bytes.set s i data.{i}
    done
  in
  (Marshal.from_bytes s 0 : 'a)

let delete (s : 'a t) = match CEphemeron.get s.proxy with
| proxy ->
  let ()  = assert proxy.valid in
  finaliser proxy
| exception CEphemeron.InvalidKey ->
  assert false
