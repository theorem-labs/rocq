(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The unit cache of the native conversion.

    A worker whose cast runs past the VM budget publishes the code of the
    definitions its conversion needs, so that the other workers load it
    instead of compiling it again. See convCache.ml for the protocol: the
    keys that decide what may be reused, the claims that keep two workers
    from compiling the same definitions, and the rules that keep the
    waits free of cycles and of orphans. *)

val enable : ?jobs:int -> unit -> unit
(** Turns the cache on and makes its directory, in the main process,
    before the first fork. It does nothing when nothing is deferred to a
    worker, so the cache, the compile slots and the units in parts are
    off with [-j 1], with [-profile] and where [Unix.fork] is not
    available. It sets [Nativelib.prepare_conversion], the compile slots
    ([jobs] of them, by default half the box's processors), and registers
    the directory's removal at exit. *)

val is_enabled : unit -> bool

(** {2 For tests only} *)

val prepare : Environ.env -> Constr.t -> Constr.t -> unit
(** What a worker does before it generates a conversion. It does nothing
    in the main process. *)

val release : unit -> unit
(** Release the claims this process holds. Every path out of [prepare]
    does this already. *)
