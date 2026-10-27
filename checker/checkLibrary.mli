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
    table of opaque proofs. The table is read the first time this process
    needs it, so this serves the main process as well as a worker. A worker
    keeps it until it exits; without workers, a table read for a library's
    checks is kept until that library's checks end, and one read after the
    walk until the process exits. *)
