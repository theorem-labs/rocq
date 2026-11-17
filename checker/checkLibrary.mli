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

val try_locate_qualified_library : object_file -> DirPath.t * physical_path
(** The library name and the file the load path gives an object file, as
    [recheck_library] resolves it: a [.vo] file is named after the logical
    path its directory is bound to.
    @raise CErrors.UserError when the library is not found. *)

val recheck_library : ?output_context:bool -> ?intern_admit:bool ->
  safe_environment ->
  norec:object_file list ->
  admit:object_file list ->
  check:object_file list -> safe_environment * Mod_checking.axioms
(** With [~intern_admit:true] (default [false]), the [admit] libraries and
    their dependencies are read too, without validation, so that an admitted
    library that no other library given here depends on is loaded as well. *)

val unchecked : unit -> DirPath.t list
(** The libraries the last [recheck_library] call imported without checking
    them. Those are the [admit] libraries with their dependencies, and the
    dependencies of the [norec] libraries that no [check] library depends
    on; the libraries given with [norec] or [check] themselves are always
    checked. *)

val indirect_accessor : Opaqueproof.opaque -> Opaqueproof.opaque_proofterm
(** The body of an opaque constant of a loaded library, from the table of
    opaque proofs that the tables in place hold for that library. *)

(** {6 The challenge side of [rocqchk -compare]} *)

type tables
(** This module's per-library tables: the loaded libraries, their tables of
    opaque proofs, the dependency graph and the load path. They are keyed by
    library name, and the challenge libraries have the solution's names, so
    the two sides each need a set of their own: the challenge is loaded
    between two [swap_tables] calls, which set the solution's tables aside
    and put them back. *)

val fresh_tables : unit -> tables
(** Empty library tables, with the load path as it is. *)

val swap_tables : tables -> tables
(** [swap_tables t] installs [t] and returns what was there. *)

type library

val intern_challenge :
  physical_path list -> DirPath.t list ->
  (DirPath.t * library) list * (DirPath.t * library) list
(** [intern_challenge files shared] reads the challenge [files] and their
    dependencies, then the [shared] libraries and theirs, in dependency
    order, without validating them and without importing any of them into an
    environment. The first result is the files' closure, the second every
    library read, the files' closure first. A library both reach is read
    once. *)

val import_challenge :
  safe_environment -> (DirPath.t * library) list -> safe_environment
(** Import the interned libraries without checking them: the challenge files
    are checked when the challenge is built, and the other libraries are
    pre-checked or shared with the solution. *)

val library_file : DirPath.t -> physical_path
(** The file the load path resolves a library name to. *)

val loaded : unit -> (DirPath.t * library) list
(** The libraries loaded so far with the tables in place: after
    [recheck_library], every library it read. *)

val deps_of : (DirPath.t * library) list -> (DirPath.t * (DirPath.t * vodigest) array) list
(** The dependency digests each library records. *)

val files_of : (DirPath.t * library) list -> (DirPath.t * physical_path) list
(** The file each library was read from, as the loader recorded it. *)

val under_root : root:DirPath.t -> DirPath.t -> bool
(** [under_root ~root lib]: whether the library name [lib] is [root] or lies
    below it, by the names they print. *)
