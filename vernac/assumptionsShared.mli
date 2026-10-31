(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The directory of Print Assumptions entries that the processes of one build
    share: the files, their claims and the key of an object. What the entries
    mean, and why reusing one cannot change an answer, is in
    {!Assumptions}. *)

open Names

(** Whether this process shares: a directory was named by
    [ROCQ_ASSUMPTIONS_SHARED_DIR] and nothing has gone wrong with it yet. Any
    failure on the directory (setting it up, a claim, a read, a write) turns
    sharing off for the rest of the process, which then walks every object
    itself. The directory must hold only what the processes of one build over
    one set of library files wrote, and those files must not change for the
    length of the build: a key covers the digests a file recorded when it was
    read, not that the file is still there and whole. *)
val usable : bool ref

(** [ROCQ_DEBUG_ASSUMPTIONS_SHARED=1]: one line per query, on standard error,
    like [ROCQ_DEBUG_ASSUMPTIONS_MEMO]. *)
val debug : bool

(** Creates the entries tree inside the directory, which must exist already;
    a failure turns sharing off. Once per process. *)
val start : unit -> unit

(** Drops the entries this process keeps in memory; it reads again from the
    directory what it needs. Called with the query cache's own reset, so that
    a process that shares keeps no more entries than one that does not. *)
val forget : unit -> unit

(** References compared by user and canonical name: the identity of an
    object. *)
module Exact : sig
  type t = GlobRef.t
  val compare : t -> t -> int
end

module EMap : Map.S with type key = Exact.t

(** What a walk of one object found: a constant or variable without a body
    and the references of its type, one with a body and its references, an
    inductive block and its references, or a walk that raised. *)
type kind = No_body | Body | Block | Failed

(** One entry, as written to the directory. *)
type found = { f_kind : kind; f_replayable : bool; f_refs : GlobRef.t list }

type claim =
  | Mine of Unix.file_descr
  (** this process holds the claim, open: locked, unless the system
      refused the lock, which only lets another process walk the object
      too *)
  | Taken  (** another process holds it *)
  | Off  (** sharing is off: the process walks every object itself *)

(** [key digests obj]: the key of an object, or of the inductive block of an
    inductive or constructor: its user and canonical names, and the content
    digests of the libraries they belong to, which [digests] gives (as
    {!Library.content_digests}); [None] for an object that is not shared: a
    section variable, an object under a functor parameter, or one of a
    library that is not loaded. *)
val key : (DirPath.t -> string option) -> GlobRef.t -> string option

(** Claims a key: the first process to create its claim gets it. *)
val claim : string -> claim

(** The claim of a key when the process that held it ended without writing
    the entry, so that its lock is free; [Taken] while a process holds it. A
    lock taken in the moment between the claimant's creating the claim and
    locking it makes two processes walk the object, which write equal
    entries. *)
val take_over : string -> claim

(** Where an entry came from, for the counters the debug line reports and the
    test reads: the directory, or this process's own index (an entry it wrote,
    or read before). *)
type source = From_directory | From_index

(** The entry of a key, read once from the directory. A file that is not a
    whole entry of that key (another build, a damaged file, a key whose MD5
    collides) counts as absent. *)
val find : string -> (source * found) option

(** Keeps the entry of a key, and writes it to the directory when this process
    holds the claim, which it then releases. *)
val publish : claim -> string -> found -> unit

(** Releases the claim of an object whose walk raised. *)
val abandon : claim -> unit
