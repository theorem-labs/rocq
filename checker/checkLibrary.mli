(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CUnix
open Names
open Safe_typing

type section_path = {
  dirpath : string list;
  basename : string;
}

type object_file =
| PhysicalFile of physical_path
| LogicalFile of section_path

type logical_path = DirPath.t

val default_root_prefix : DirPath.t

val add_load_path : physical_path * logical_path -> unit

val recheck_library : safe_environment ->
  norec:object_file list ->
  admit:object_file list ->
  check:object_file list -> safe_environment * Cset.t Cmap.t

val indirect_accessor : Opaqueproof.opaque -> Opaqueproof.opaque_proofterm
(** The body of an opaque constant of a loaded library, from that library's
    table of opaque proofs. The table is read, and kept, the first time this
    process needs it, so this serves the main process as well as a worker. *)

(** {6 The challenge side of [rocqchk -compare]} *)

type tables
(** This module's per-library tables: the loaded libraries, their tables of
    opaque proofs, the dependency graph and the load path. They are keyed by
    library name, and the challenge libraries have the answer's names, so the
    two sides each need a set of their own. *)

val fresh_tables : unit -> tables
(** Empty library tables, with the load path as it is. *)

val swap_tables : tables -> tables
(** [swap_tables t] installs [t] and returns what was there. *)

type challenge_library

val intern_challenge :
  physical_path list -> DirPath.t list ->
  (DirPath.t * challenge_library) list * (DirPath.t * challenge_library) list
(** [intern_challenge files shared] reads the challenge [files] and their
    dependencies, then the [shared] libraries and theirs, in dependency
    order, without importing any of them into an environment. The first
    result is the files' closure, the second every library read, the files'
    closure first. A library both reach is read once. *)

val challenge_deps :
  (DirPath.t * challenge_library) list -> (DirPath.t * (DirPath.t * vodigest) array) list
(** The dependency digests each interned library records. *)

val challenge_files :
  (DirPath.t * challenge_library) list -> (DirPath.t * physical_path) list
(** The file each interned library was read from, as the loader recorded
    it. *)

val import_challenge :
  safe_environment -> (DirPath.t * challenge_library) list -> safe_environment
(** Import the interned libraries without checking them. *)

val library_file : DirPath.t -> physical_path
(** The file the load path resolves a library name to. *)

val interned_deps : unit -> (DirPath.t * (DirPath.t * vodigest) array) list
(** The dependency digests every library interned so far records. *)

val interned_files : unit -> (DirPath.t * physical_path) list
(** The file each library loaded so far was read from, as the loader
    recorded it. *)
