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

val set_location_free_label : bool -> unit
(** [-location-free-label]: when [true], a saved library stores as the
    digest of its [library] segment the first 16 bytes of the location-free
    label of its summary and [library] segment ([LibkeyObjects.label])
    instead of the MD5 of the segment's bytes, and stores the attempted
    resolutions nothing else records ([Attempts]). Default [false]: the
    file is what a stock [coqc] writes. A stock [coqc] cannot load a
    library that holds an [ATTEMPTS] object (it does not know the object
    kind). *)

(** What [rocq-library-label] reads in a [.vo] file. The two digests are
    computed when they are forced: a reader that only wants the records
    pays for neither. *)
type file_label = {
  name : DirPath.t;
  (** The library's logical name, from its [summary] segment. *)
  stored : string;
  (** The digest the file stores for its [library] segment: what its
      dependents record. *)
  segment_md5 : string Lazy.t;
  (** The MD5 of that segment's bytes: what stock stores there. *)
  label : (string, string) result Lazy.t;
  (** The label (32 bytes) recomputed from the file's [summary] and
      [library] segments ([LibkeyObjects.label_result]), or why the library
      has none. *)
  attempts : Attempts.t option;
  (** The attempted-resolution records of its object segment. *)
  axiom_report : LibkeyObjects.axiom_report Lazy.t;
  (** The constants the label blinded, with their current status, and the
      libraries this one holds a foreign opaque reference into
      ([LibkeyObjects.axiom_report]): what the keep rule reads beside the
      label for its monotone axiom condition. *)
  keep_facts : KeepFacts.t option;
  (** Its [keepfacts] segment ([KeepFacts]): the assumption closure and the
      foreign opacities its strategy commands saw. [None] for a file written
      without [-location-free-label], or a [.vos]; the keep rule then rebuilds. *)
}

val read_file_label : CUnix.physical_path -> file_label
(** Raises an exception when the file cannot be read as a [.vo] file. *)

(** {6 Interrogate the status of libraries } *)

  (** - Tell if a library is loaded *)
val library_is_loaded : DirPath.t -> bool

(** - Tell which libraries are loaded, in the order by which they were loaded. *)
val loaded_libraries : unit -> DirPath.t list

val library_compiled : DirPath.t -> Safe_typing.compiled_library

(** {6 Native compiler. } *)
val native_name_from_filename : string -> string

(** {6 Opaque accessors} *)
val indirect_accessor : Global.indirect_accessor
[@@deprecated
  "(8.20) Most commands should not be accessing opaque data. \
   Use coqpp's \"opaque_access\" state specifier if you actually need it."]
