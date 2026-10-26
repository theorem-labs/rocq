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

(** Records of attempted resolutions (design D18, dispatch://INFRA-361,
    spec item 3).

    A [Require], [Load] or [Declare ML Module] that a library attempted can
    leave no trace in it: a command under [Fail] or [Succeed] is rolled
    back, so a [Require] there is in neither the library's dependencies nor
    [rocq dep]'s output, and a [Load] never leaves an object. The outcome of
    the library's compilation still depended on what the attempt found. So
    every attempt is logged while a library is compiled, outside the state
    that a rollback restores, and the library stores the attempts that
    nothing else records in one [ATTEMPTS] object of its object segment: a
    [Require] whose library is not loaded when the library is saved (it
    failed, or it was rolled back), every [Load], and a [Declare ML Module]
    whose plugin is not loaded then. A library that made no such attempt
    gets no object, so its file is what a stock [coqc] writes.

    Each record holds what the attempt looked for and found: the request;
    every candidate file it could probe, with whether that file existed; the
    files it read, with the SHA-256 of each when the library was saved; and,
    for a [Require] or a [Load], the load path it searched, with the
    subdirectories of each directory that a recursive scan would make load
    path entries (a new one can make a failed lookup succeed). For a
    [Declare ML Module], the plugin's files as findlib resolved them.

    The object is in the library segment, so the library's label
    ([LibkeyObjects]), which reads it as it is and which coqc stores as the
    library's digest, covers the records: a library compiled where an
    attempt finds something else is a different library.
    Paths are absolute, so the same file compiled in another directory has
    other records. *)

type t

(** {6 Logging, while a library is compiled} *)

val set_enabled : bool -> unit
(** Log attempts ([true]) or ignore every [record_*] call ([false], the
    default; the [probes] functions are then not called). [Library.set_location_free_label] sets it: the records are
    written only under [-location-free-label]. *)

val reset : unit -> unit
(** Forget the attempts logged so far. *)

val record_require_qualified :
  root:DirPath.t option -> Libnames.qualid -> probes:(unit -> (string * string) list) ->
  library:DirPath.t option -> found:string option -> unit
(** A [Require] of a (partially) qualified name: the candidate files
    (directory, file name), the library it resolved to and its file, if any. *)

val record_require_absolute :
  DirPath.t -> probes:(unit -> (string * string) list) -> found:string option -> unit
(** The lookup of a library's file by its full name, for a [Require]'s root
    or one of the dependencies it interns. *)

val record_load : string -> probes:(unit -> (string * string) list) -> found:string option -> unit
(** A [Load] of a file name. *)

val record_ml_module : string -> unit
(** A [Declare ML Module] of a plugin (findlib name), resolved with the
    resolver [set_plugin_resolver] installed. *)

val set_plugin_resolver : (string -> string list option) -> unit
(** How a plugin name resolves to its files ([None]: no such plugin).
    [Mltop] installs findlib's resolution. *)

(** {6 Saving and reading} *)

val finish : loaded:(DirPath.t -> bool) -> loaded_plugin:(string -> bool) -> t option
(** The records the library being saved keeps: the attempts that nothing
    else records ([loaded]: whether a library is loaded at the end of the
    file; [loaded_plugin]: whether a plugin is), with the digests of the
    files they read. [None] if there are none. *)

val inject : t -> Libobject.obj
(** The [ATTEMPTS] object (a [Keep] object that the library label reads as
    it is). *)

val find : Declaremods.library_objects -> t option
(** The records a library's object segment holds. *)

val describe : t -> string list
(** One line per record: the request, each candidate with whether it was
    found, and each file read with its SHA-256. *)
