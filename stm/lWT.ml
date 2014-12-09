(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2014     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util

module Queue =
struct

include Queue

(** Helper function: push on top of a queue. *)
let hsup x q =
  let tmp = Queue.create () in
  let () = Queue.transfer q tmp in
  let () = Queue.push x q in
  Queue.transfer tmp q

end

type 'a result =
| Ans of 'a
| Err of exn

type 'a comp = ('a -> unit) -> unit

type ops = {
  yield : unit comp;
  (** Push the computation with lowest priority *)
  still : unit comp;
  (** Push the computation with highest priority *)
  join : 'a 'b. 'a result comp -> 'b result comp -> ('a * 'b) result comp;
  wait_rd : Unix.file_descr -> (unit -> unit) -> unit;
  wait_wr : Unix.file_descr -> (unit -> unit) -> unit;
  wait_id : int -> (Unix.process_status -> unit) -> unit;
  exit : unit -> unit;
}

type 'a t = ops -> ('a result -> unit) -> unit

type pid = int

type loop = {
  last_id : int ref;
  watched : (unit -> unit) Int.Map.t ref;
  pending : (unit -> unit) Queue.t;
  reading : (Unix.file_descr * (unit -> unit)) list ref;
  writing : (Unix.file_descr * (unit -> unit)) list ref;
  waiting : (pid * (Unix.process_status -> unit)) list ref;
}

let loop () = {
  last_id = ref 0;
  watched = ref Int.Map.empty;
  pending = Queue.create ();
  reading = ref [];
  writing = ref [];
  waiting = ref [];
}

let return x = (); fun _ k -> k (Ans x)

let bind m f = (); fun ops k ->
  let next = function
  | Ans x -> f x ops k
  | Err _ as e -> k e
  in
  m ops next

let raise e = (); fun _ k -> k (Err e)

let catch m f = (); fun ops k ->
  let next ans = match ans with
  | Ans _ -> k ans
  | Err e -> f e ops k
  in
  m ops next

let dummy_ans = Ans ()

let yield = fun ops k -> ops.yield (fun () -> k dummy_ans)

let exit = fun ops _ -> ops.exit ()

(** The run_* functions return a boolean indicating whether they made
    progress. *)

let run_fdescrs loop = match !(loop.reading), !(loop.writing) with
| [], [] -> false
| rl, wl ->
  let rok = List.map fst rl in
  let wok = List.map fst wl in
  let rok, wok, _ = Unix.select rok wok [] 0. in
  match rok, wok with
  | [], [] -> false
  | _ ->
    let rec filter mem accu = function
    | [] -> accu
    | (fd, k as item) :: rem ->
      if List.mem fd mem then
        let () = Queue.hsup k loop.pending in
        filter mem accu rem
      else
        filter mem (item :: accu) rem
    in
    let rl = filter rok [] rl in
    let wl = filter wok [] wl in
    let () = loop.reading := rl in
    let () = loop.writing := wl in
    true

let run_waiting loop =
  if List.is_empty !(loop.waiting) then false
  else
    let rec check_waiting accu = function
    | [] -> None
    | (id, k as item) :: rem ->
      let ans, stat = Unix.waitpid [Unix.WNOHANG] id in
      if ans = 0 then check_waiting (item :: accu) rem
      else
        let () = Queue.hsup (fun () -> k stat) loop.pending in
        Some (List.rev_append accu rem)
    in
    match check_waiting [] !(loop.waiting) with
    | None -> false
    | Some r -> loop.waiting := r; true

let run_pending loop =
  if Queue.is_empty loop.pending then false
  else
    let f = Queue.pop loop.pending in
    let () = f () in
    true

let is_finished loop =
  Queue.is_empty loop.pending &&
  List.is_empty !(loop.reading) &&
  List.is_empty !(loop.writing) &&
  List.is_empty !(loop.waiting)

let step_loop loop =
  ignore (run_fdescrs loop || run_pending loop || run_waiting loop)

let rec run_loop loop =
  if is_finished loop then ()
  else
    let () = step_loop loop in
    run_loop loop

let rec run_loop_until_idle loop =
  if run_fdescrs loop || run_pending loop || run_waiting loop then
    run_loop_until_idle loop

type ('a, 'b) opt_val =
| Nul
| Inl of 'a
| Inr of 'b

let mix x y = match x, y with
| Ans x, Ans y -> Ans (x, y)
| Err e, _ -> Err e
| _, Err e -> Err e

let join_ loop x y = (); fun k ->
  let ans = ref Nul in
  let kx x = match !ans with
  | Nul -> ans := Inl x
  | Inl _ -> assert false
  | Inr y -> k (mix x y)
  in
  let ky y = match !ans with
  | Nul -> ans := Inr y
  | Inl x -> k (mix x y)
  | Inr _ -> assert false
  in
  let cx () = x (fun x -> kx x) in
  let cy () = y (fun y -> ky y) in
  let () = Queue.hsup cx loop.pending in
  let () = Queue.hsup cy loop.pending in
  ()

let detach m = (); fun ops k ->
  ops.yield (fun () -> m ops ignore)

let join x y = (); fun ops k ->
  ops.join (fun k -> x ops k) (fun k -> y ops k) k

let signal id loop =
  try Int.Map.find id !(loop.watched) () with Not_found -> ()

let make_ops id loop =
  (** Yielding delays the thread as the last one on the queue *)
  let yield k = Queue.push k loop.pending in
  let still k = Queue.hsup k loop.pending in
  let exit () = signal id loop in
  {
    yield = yield;
    still = still;
    join = (fun x y -> join_ loop x y);
    wait_rd = (fun descr k -> loop.reading := (descr, k) :: !(loop.reading));
    wait_wr = (fun descr k -> loop.writing := (descr, k) :: !(loop.writing));
    wait_id = (fun pid k -> loop.waiting := (id, k) :: !(loop.waiting));
    exit = exit;
  }

exception Exited

let run t =
  let loop = loop () in
  let ops = make_ops 0 loop in
  let ans = ref None in
  let next res = ans := Some res in
  let f () = t ops next in
  let () = Queue.hsup f loop.pending in
  let () = run_loop loop in
  match !ans with
  | None ->
    (** Thread exited before returning *)
    Pervasives.raise Exited
  | Some (Ans x) -> x
  | Some (Err e) -> Pervasives.raise e

type id = int

let add_loop t loop =
  let id = !(loop.last_id) in
  let () = incr loop.last_id in
  let ops = make_ops id loop in
  let finish _ = signal id loop in
  let f () = t ops finish in
  let () = Queue.hsup f loop.pending in
  id

let run_loop_until loop id =
  let alive = ref true in
  (** Save the old watched thread *)
  let watched = !(loop.watched) in
  let signal () = alive := false in
  let () = loop.watched := Int.Map.singleton id signal in
  let () = while !alive do step_loop loop done in
  loop.watched := watched

type mutex = {
  lock : bool ref;
  locked : (unit -> unit) Queue.t;
}

module Mutex =
struct
  let create () = {
    lock = ref false;
    locked = Queue.create ();
    (** Contains functions unlocking each thread *)
  }

  let rec lock m = (); fun ops k ->
    if !(m.lock) then
      let unlock () = ops.still (fun () -> lock m ops k) in
      Queue.push unlock m.locked
    else
      let () = m.lock := true in
      k dummy_ans

  let unlock m =
    let () = m.lock := false in
    if not (Queue.is_empty m.locked) then
      Queue.pop m.locked ()

  let is_locked m = !(m.lock)

end

type condition = (unit -> unit) Queue.t

module Condition =
struct
  let create = Queue.create

  let wait c m = (); fun ops k ->
    let () = assert (!(m.lock)) in
    let () = m.lock := false in
    let unlock () = ops.still (fun () -> Mutex.lock m ops k) in
    Queue.push unlock c

  let await c = (); fun ops k ->
    let unlock () = ops.still (fun () -> k dummy_ans) in
    Queue.push unlock c

  let signal c =
    if not (Queue.is_empty c) then
      Queue.pop c ()

  let broadcast c =
    while not (Queue.is_empty c) do
      Queue.pop c ();
    done

end

module Unix =
struct
  open Unix
  type file_descr = Unix.file_descr

  let rec read descr buf off len = (); fun ops k ->
    try
      let ans = Unix.read descr buf off len in
      return ans ops k
    with
    | Unix_error ((EAGAIN | EWOULDBLOCK | EINTR), _, _) ->
      ops.wait_rd descr (fun () -> read descr buf off len ops k)
    | e -> raise e ops k

  let rec write descr buf off len = (); fun ops k ->
    try
      let ans = Unix.single_write descr buf off len in
      return ans ops k
    with
    | Unix_error ((EAGAIN | EWOULDBLOCK | EINTR), _, _) ->
      ops.wait_wr descr (fun () -> write descr buf off len ops k)
    | e -> raise e ops k

  let wait_rd descr = (); fun ops k ->
    ops.wait_rd descr (fun () -> k dummy_ans)

  let wait_wr descr = (); fun ops k ->
    ops.wait_wr descr (fun () -> k dummy_ans)

  let waitpid id = (); fun ops k ->
    ops.wait_id id (fun ans -> k (Ans ans))

end

module Notations =
struct
  let (>>=) = bind
  let (<*>) x y = bind x (fun () -> y)
end
