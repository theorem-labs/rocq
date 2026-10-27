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

(** The location-free label of a library (design D18, dispatch://INFRA-361).

    [coqc -location-free-label] stores the first 16 bytes of the label as
    the digest of a library's [library] segment, in place of the MD5 of that
    segment's bytes ([Library.save_library_to]). Stock [coqc] and [rocqchk]
    never recompute the digest; they compare the copy a dependent recorded
    with the copy the library's file stores. A library rebuilt from a source
    that differs only in where its text sits (comments, blank lines, spaces)
    or inside an opaque proof (whose term is in another segment) gets the
    same label, unless the edit creates a new universe (below), so its
    dependents keep their compiled files.

    {b Byte layout, version 2.} The label is
    {v Libkey.label (Obj.repr (version, compiled, syn', obj', summary')) v}
    (32 bytes) where:
    - [compiled] is the library's compiled form as stored (its dependencies'
      digests included, so a label covers what a library was compiled
      against);
    - [syn'] and [obj'] are its two object segments with the same tree of
      module, module type, include, keep, escape and export entries, in the
      same order, and each atomic object replaced by its view
      [Libobject.interface_object]: the object itself when its kind declares
      [Key_as_is], or its copy through the typed stripper of its kind
      ([Key_stripped]), which sets every source location to a fixed value
      and changes nothing else. The container entries hold no source
      location and are kept as they are. An ML-MODULE object is read as it
      is stored, with the digests of its plugins' files when the library was
      compiled. The [ATTEMPTS] object ([Attempts]) is read as it is stored;
    - [summary'] is the library's summary, the segment that a dependent's
      [Require] reads first: [(name, deps, safe_deps, (depr, warns))], with
      [name] the library's logical name, [deps] its direct dependencies in
      their order with the digests it was compiled against (a list of
      [(DirPath.t, Safe_typing.vodigest)] pairs), [safe_deps] the ones of
      them it only safe-required ([Require (safe)]), in [DirPath.compare]
      order, [depr] its deprecation attribute as
      [(since, note) option] and [warns] its warning attributes as a list of
      [(note, categories)]. These are names, digests and strings: the
      summary holds no source location and no file path. The OCaml version
      the summary also records is in [Libkey]'s header.

    Version 1 had no [summary']: two builds of a library that differed only
    in a [Require] made [Require (safe)] had the same label, although a
    dependent that also requires the dependency fully compiles against one
    and fails against the other (Astra review of version 1, section 3.1).

    Universe names and bound-module counters are read as they are: they
    escape into the dependents (a dependent that applies a functor stores
    the functor's identifier), so two libraries in which they differ must
    have different labels. A proof-only edit that makes the elaboration
    create one more universe renumbers every later universe of the file,
    and so changes the label.

    A library has no label (the functions return [None] or [Error]) when it
    holds an object whose kind declares [Not_in_key] or is not registered,
    when a stripper meets a value it cannot strip by type (an unregistered
    generic argument, ...), or when [Libkey.encode] meets a value it does
    not define. Such a library gets stock's digest, the MD5 of its segment's
    bytes.

    The version changes whenever this layout or the meaning of a kind's
    view changes (a kind that starts being stripped, a stripper that starts
    reaching a new field), so that labels made by different views never
    match. *)

val version : int

(** The summary of a library, as [Library] writes it in a [.vo] file's
    [summary] segment (but for the OCaml version). *)
type summary = {
  name : DirPath.t;
  deps : (DirPath.t * Safe_typing.vodigest) array;
  (** The direct dependencies, in their order, with their digests. *)
  safe_deps : DirPath.Set.t;
  (** The direct dependencies that were only safe-required. *)
  info : Library_info.t;
  (** The library's attributes. *)
}

val strip_segment :
  Declaremods.library_objects -> (Declaremods.library_objects, string) result
(** The segment as the label reads it ([syn'] or [obj'] above). [Error what]
    names the first object that has no view. *)

val label_result :
  summary:summary -> compiled:Safe_typing.compiled_library ->
  syntax:Declaremods.library_objects -> objects:Declaremods.library_objects ->
  (string, string) result
(** The 32-byte label, or why the library has none. *)

val label :
  summary:summary -> compiled:Safe_typing.compiled_library ->
  syntax:Declaremods.library_objects -> objects:Declaremods.library_objects ->
  string option
