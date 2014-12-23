(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open LWT.Notations

module Mutex = LWT.Mutex
module Condition = LWT.Condition

module PriorityQueue : sig
  type 'a t
  val create : unit -> 'a t
  val set_rel : ('a -> 'a -> int) -> 'a t -> unit
  val is_empty : 'a t -> bool
  val exists : ('a -> bool) -> 'a t -> bool
  val pop : ?picky:('a -> bool) -> 'a t -> 'a
  val push : 'a t -> 'a -> unit
  val clear : 'a t -> unit
end = struct
  type 'a item = int * 'a
  type 'a rel = 'a item -> 'a item -> int
  type 'a t = ('a item list * 'a rel) ref
  let sort_timestamp (i,_) (j,_) = i - j
  let age = ref 0
  let create () = ref ([],sort_timestamp)
  let is_empty t = fst !t = []
  let exists p t = List.exists (fun (_,x) -> p x) (fst !t)
  let pop ?(picky=(fun _ -> true)) ({ contents = (l, rel) } as t) =
    let rec aux acc = function
      | [] -> raise Queue.Empty
      | (_,x) :: xs when picky x -> t := (List.rev acc @ xs, rel); x
      | (_,x) as hd :: xs -> aux (hd :: acc) xs in
    aux [] l
  let push ({ contents = (xs, rel) } as t) x =
    incr age;
    (* re-roting the whole list is not the most efficient way... *)
    t := (List.sort rel (xs @ [!age,x]), rel)
  let clear ({ contents = (l, rel) } as t) = t := ([], rel)
  let set_rel rel ({ contents = (xs, _) } as t) =
    let rel (_,x) (_,y) = rel x y in
    t := (List.sort rel xs, rel)
end

type 'a t = {
  queue: 'a PriorityQueue.t;
  cond : LWT.condition;
  mutable nwaiting : int;
  cond_waiting : LWT.condition;
  mutable release : bool;
}

exception BeingDestroyed

let create () = {
  queue = PriorityQueue.create ();
  cond = Condition.create ();
  nwaiting = 0;
  cond_waiting = Condition.create ();
  release = false;
}

let pop ?(picky=(fun _ -> true)) ?(destroy=ref false)
  ({ queue = q; cond = c; cond_waiting = cn } as tq)
=
  let rec waiting () =
    if tq.release || !destroy then
      LWT.raise BeingDestroyed
    else if PriorityQueue.exists picky q then
      let x = PriorityQueue.pop ~picky q in
      let () = Condition.signal c in
      let () = Condition.signal cn in
      LWT.return x
    else
      let () = tq.nwaiting <- tq.nwaiting + 1 in
      let () = Condition.broadcast cn in
      Condition.await c >>= fun () ->
      let () = tq.nwaiting <- tq.nwaiting - 1 in
      waiting ()
  in
  waiting ()

let signal_destruction { cond = c } =
  Condition.broadcast c

let push { queue = q; cond = c; release } x =
  if release then Errors.anomaly(Pp.str
    "TQueue.push while being destroyed! Only 1 producer/destroyer allowed");
  PriorityQueue.push q x;
  Condition.broadcast c

let clear { queue = q; cond = c } =
  PriorityQueue.clear q

let is_empty { queue = q } = PriorityQueue.is_empty q

let destroy tq =
  tq.release <- true;
  let rec loop () =
    if tq.nwaiting > 0 then
      let () = Condition.broadcast tq.cond in
      LWT.yield >>= loop
    else
      let () = tq.release <- false in
      LWT.return ()
  in
  loop ()

let rec wait_until_n_are_waiting_and_queue_empty j tq =
  if not (PriorityQueue.is_empty tq.queue) || tq.nwaiting < j then
    Condition.await tq.cond_waiting >>= fun () ->
    wait_until_n_are_waiting_and_queue_empty j tq
  else LWT.return ()

let wait_until_n_are_waiting_then_snapshot j tq =
  let l = ref [] in
  while not (PriorityQueue.is_empty tq.queue) do
    l := PriorityQueue.pop tq.queue :: !l
  done;
  let rec waiting () =
    if tq.nwaiting < j then Condition.await tq.cond_waiting >>= waiting
    else
      let () = List.iter (PriorityQueue.push tq.queue) (List.rev !l) in
      let () = if !l <> [] then Condition.broadcast tq.cond in
      LWT.return (List.rev !l)
  in
  waiting ()

let set_order tq rel =
  PriorityQueue.set_rel rel tq.queue
