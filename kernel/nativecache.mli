(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** A content-addressed, cross-process cache of compiled native-conversion
    units. The checker's native conversion ({!Nativeconv}) splits the code of
    a cast's dependency closure into bounded units
    ({!Nativelib.link_dependencies}) and compiles each once; this module lets
    every process that shares the cache directory ([ROCQCHK_NATIVE_CACHE])
    reuse a unit another process already compiled. Without that variable the
    cache is a private directory, shared with the [-j] workers and removed
    when the main process exits.

    Safety invariant: an entry is addressed by a SHA-256 of the unit's
    generated source, the digests of the compiled artifacts of every earlier
    unit it names, and an "epoch" fingerprint of every component that can
    change what the source compiles to (this coqchk binary, the resolved
    [ocamlfind]/[ocamlopt], the compiler flags, the kernel's native [.cmi]
    tree). The unit's module name is derived from that key. Entries are never
    invalidated: a stale entry from another toolchain is simply never looked
    up. *)

(** [init ~include_dirs ~flags] fixes the cache root and the epoch. It must
    run once, before any native conversion and before any [-j] worker is
    forked. [include_dirs] and [flags] are those of every unit compile. *)
val init : include_dirs:string list -> flags:string list -> unit

(** [key ~text ~deps]: hex key of a unit whose generated source is [text] and
    whose referenced earlier units have the artifact digests [deps]. *)
val key : text:string -> deps:string -> string

val mkdir_p : string -> unit

val copy_file : src:string -> dst:string -> unit

val absolute : string -> string

(** Number of hex digits of the key in a unit's module name. *)
val module_name_len : int

(** OCaml module name of the unit with this key. *)
val module_name : string -> string

(** Extension of the loadable object of a unit. *)
val object_ext : string

(** Directory of the published entry for this key, if any (counts a hit). It
    holds the unit's object, [.cmi] and (native) [.cmx], each named after
    {!module_name}. *)
val lookup : string -> string option

(** Count one unit that had to be compiled. *)
val note_miss : unit -> unit

(** [with_lock key f] runs [f] holding an exclusive cross-process lock scoped
    to this key (a POSIX [lockf], released if the holder dies). Callers MUST
    re-run {!lookup} after acquiring it. Locks are held for one unit at a
    time and never nested. *)
val with_lock : string -> (unit -> 'a) -> 'a

(** The message recorded by {!record_failure} for this key in this run, if
    any. A worker that finds one fails with it instead of compiling again. *)
val failure_of : string -> string option

val record_failure : string -> string -> unit

(** A fresh private directory inside the cache for compiling the unit with
    this key (same filesystem as the entry, so {!publish} is a rename). The
    compile must run with it as its working directory and name its source
    relatively, so that the artifacts do not depend on where they were built. *)
val scratch : string -> string

(** [publish key ~scratch] keeps only the unit's object, [.cmi] and [.cmx] of
    [scratch], renames it to the entry directory and returns that directory
    (an entry that already exists wins). *)
val publish : string -> scratch:string -> string

val discard_scratch : string -> unit

(** Digest of the [.cmi] and [.cmx] of a stored unit. *)
val artifact_digest : dir:string -> name:string -> string

val reset_stats : unit -> unit

(** One-line summary of this process's hits / misses / lock-wait time. *)
val stats_line : unit -> string
