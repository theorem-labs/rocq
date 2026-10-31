(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** This module provides functions to load, open and save
  libraries. Libraries correspond to the subclass of modules that
  coincide with a file on disk (the ".vo" files). Libraries on the
  disk comes with checksums (obtained with the [Digest] module), which
  are checked at loading time to prevent inconsistencies between files
  written at various dates.
*)

(** Type of libraries loaded in memory *)
type library_t

(** Whether a library of a required closure is fully loaded (its objects are
    replayed) or only safe-loaded (imported kernel-side, full-qualified names
    only). *)
type require_mode = ModeFull | ModeSafe

(** {6 ... }
    Require = load in the environment *)
val require_library : (require_mode * library_t) list -> unit

(** Intern from a .vo file located by libresolver *)
module Intern : sig
  module Provenance : sig
    type t = string * string
    (** A pair of [kind, object], for example ["file",
        "/usr/local/foo.vo"], used for error messages. *)
  end

  type t = DirPath.t -> (library_t, Exninfo.iexn) Result.t * Provenance.t
end

val intern_from_file : CUnix.physical_path ->
  (library_t, Exninfo.iexn) Result.t * Intern.Provenance.t

(** Intern the dependency closure of the given roots, compute per-library
    modes ([cmd_safe] is the command mode: [false] for [Require], [true] for
    [Require (safe)]), register the syntactic part and return the interp-side
    closure tagged with the computed modes. *)
val require_library_syntax_from_dirpath
  : cmd_safe:bool
  -> intern:Intern.t
  -> DirPath.t Loc.located list
  -> (require_mode * library_t) list

(** {6 Start the compilation of a library } *)

(** End the compilation of a library and save it to a ".vo" file, or a
    ".vos" file, depending on the todo_proofs argument.

    [output_native_objects]: when producing vo objects, also compile
    the native-code version. *)

type 'doc todo_proofs =
 | ProofsTodoNone (* for .vo *)
 | ProofsTodoSomeEmpty of Future.UUIDSet.t (* for .vos *)

val save_library_to :
  'document todo_proofs ->
  output_native_objects:bool ->
  DirPath.t -> string -> unit

(** Save library to library_t format, that can be used later in
    [require_library_syntax_from_dirpath] *)
val save_library : DirPath.t -> library_t

(** {6 The opaque proofs of a registered object (BET-84)} *)

val opaques_segment_sha256 : string -> string option
(** The SHA-256 of the opaque-proof segment's bytes in the object file
    [f], as 64 hex digits; [None] when [f] cannot be read or is not an
    object file of this version. *)

val registered_opaques :
  file:string -> sha256:string -> (Opaques.opaque_disk, string) result
(** The opaque proofs of the object file [file], when the bytes of that
    segment hash to [sha256]. The file is read once, so the bytes hashed
    are the bytes read back. [Error "missing"] when the file cannot be read,
    [Error "changed"] when it is not such an object or the segment differs. *)

(** {6 Interrogate the status of libraries } *)

  (** - Tell if a library is loaded *)
val library_is_loaded : DirPath.t -> bool

(** - Tell which libraries are loaded, in the order by which they were loaded. *)
val loaded_libraries : unit -> DirPath.t list

(** - The digest of a loaded library's [.vo], as 32 hex digits, and
      ["unknown"] for a library that is not loaded. *)
val library_digest : DirPath.t -> string

(** - Those loaded libraries that were only safe-loaded ([Require (safe)],
      or a safe dependency of a loaded library), in load order. *)
val safe_loaded_libraries : unit -> DirPath.t list

val library_compiled : DirPath.t -> Safe_typing.compiled_library

(** {6 Native compiler. } *)
val native_name_from_filename : string -> string

(** {6 Opaque accessors} *)
val indirect_accessor : Global.indirect_accessor
[@@deprecated
  "(8.20) Most commands should not be accessing opaque data. \
   Use coqpp's \"opaque_access\" state specifier if you actually need it."]
