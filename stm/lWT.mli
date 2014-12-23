(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2014     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Cooperative threads.

  A cooperative thread is a datastructure allowing cooperative multitasking and
  transparent non-blocking IO.

  Contrarily to native threads, thread switching is only done when the thread
  allows it, through a {!yield} action for instance. This ensures atomicity of
  actions by mere typing: whenever a code is not in the threaded type, it cannot
  be stolen from the current control.

  All functions in this module are non-blocking, except if specified otherwise.
*)

type +'a t
(** Type of cooperative threads *)

(** {6 Monadic interface} *)

val return : 'a -> 'a t
(** Create a thread from a value. *)

val bind : 'a t -> ('a -> 'b t) -> 'b t
(** Compose threads. Control may be given back to other threads. *)

(** {6 Primitives} *)

val raise : exn -> 'a t
(** Raise the given exception. *)

val catch : 'a t -> (exn -> 'a t) -> 'a t
(** Try-catch clause. *)

val yield : unit t
(** Return control to the scheduler. *)

val exit : 'a t
(** Exit the thread. *)

val join : 'a t -> 'b t -> ('a * 'b) t
(** Synchronizes on the two values. Respective order of evaluation is not
    specified, and may be interleaved. *)

val detach : 'a t -> unit t
(** [detach m] executes [m] in parallel to the current thread, without blocking
    it. The result is discarded and any uncaught exception is ignored. *)

(** {6 Running threads} *)

val run : 'a t -> 'a
(** Creates its own loop, and run the given thread inside it. This blocks until
    all of the threads fed to the loop have answered. *)

type loop

type id

val loop : unit -> loop
val add_loop : 'a t -> loop -> id
val run_loop : loop -> unit
val run_loop_until : loop -> id -> unit
val run_loop_until_idle : loop -> unit

(** {6 Concurrency structures} *)

type mutex
type condition

module Mutex :
sig
  val create : unit -> mutex
  val lock : mutex -> unit t
  val unlock : mutex -> unit
  val is_locked : mutex -> bool
end

module Condition :
sig
  val create : unit -> condition
  val wait : condition -> mutex -> unit t
  val await : condition -> unit t
  val signal : condition -> unit
  val broadcast : condition -> unit
end

(** {6 Unix bindings} *)

module Unix :
sig
  type file_descr = Unix.file_descr
  val read : file_descr -> string -> int -> int -> int t
  val write : file_descr -> string -> int -> int -> int t
  val wait_rd : file_descr -> unit t
  val wait_wr : file_descr -> unit t
  val waitpid : int -> Unix.process_status t
end
(** Non-blocking versions of Unix primitives. *)

module Notations :
sig
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
  val (<*>) : unit t -> 'a t -> 'a t
end
