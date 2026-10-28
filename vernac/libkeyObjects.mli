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
    - [compiled] is the library's compiled form as stored. It holds the
      digests its dependencies' files stored when this library was compiled
      against them. Such a digest covers a dependency's own summary only
      when it is itself a version-2 label: for a dependency compiled
      without [-location-free-label], or one that has no label, it is the
      MD5 of that dependency's [library] segment, which its summary is not
      part of. So a reuse decision must require a version-2 label
      ([rocq-library-label --check] says [label2]) of every library of the
      cone, not of the candidate alone;
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
    match.

    {b The axiom-or-opaque-proof blinding (version 3, S1b).} A constant whose
    body is [Undef None] (an axiom or parameter with no body, as [Admitted]
    and [Axiom] make) and one whose body is [OpaqueDef _] (an opaque proof, as
    [Qed] makes) give the {e same} label contribution: the label reads their
    type, universe context and constraints, typing and guard flags, section
    data, relevance and inline mark, but not the axiom-or-opaque distinction
    nor the opaque table index ([blind_constant]). [Admitted -> Qed] and
    [Qed -> Admitted] therefore keep the label. A transparent body ([Def]),
    which conversion unfolds, is {e not} blinded, and neither is an inlinable
    parameter ([Undef (Some _)]), whose inline level a functor application
    observes. The blinding is sound because a dependent never observes the
    erased difference (kernel/environ.ml:654-677, vmbytegen.ml:988-990,
    genlambda.ml:797-798); its two consequences the label no longer carries --
    the library's assumption set and which opaque proof a foreign [Indirect]
    reference resolves to -- are the keep rule's monotone axiom condition and
    its foreign-opaque-reference check, fed by [axiom_report].

    {b What the label does not cover.} The [opaques] segment (the proof
    terms of opaque constants: a changed proof keeps the label unless it
    changes what the compiled form holds, which is the point of the
    design, so its owning library must still reach the proof checker), the
    [vm] segment, which the checker regenerates, and the native sidecar
    files beside the [.vo]. A [.vos] built from a source has the same
    summary and [library] segments as its [.vo], and so the same label.
    The OCaml version is in [Libkey]'s header, so it is covered for a file
    whose stored digest has been checked against a label recomputed by a
    tool of the same build, not for one read as it is. The keep rule that
    reads labels handles all of these. *)

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

val blind_constant : Declarations.constant_body -> Declarations.constant_body
(** A constant whose body is [Undef None] or [OpaqueDef _] replaced by the
    canonical [Undef None], every other field kept; [Def], [Primitive],
    [Symbol] and [Undef (Some _)] left as they are (S1b). *)
val blind_compiled :
  Safe_typing.compiled_library -> Safe_typing.compiled_library
(** The compiled library as the label reads it: every constant with an
    [OpaqueDef] or [Undef None] body replaced by a canonical [Undef None]
    ([blind_constant]). Idempotent. A view for computing the label; the kernel
    never loads this. *)

(** The assumption status of a blinded constant: [Axiom] is a body of
    [Undef None], [Proof] a body of [OpaqueDef _]. *)
type assumption_status = Axiom | Proof

(** What the keep rule reads beside the label to apply its monotone axiom
    condition and its foreign-opaque-reference check (C1, dispatch://INFRA-361).
    Both are computed from the current compiled form, never recorded. *)
type axiom_report = {
  blinded : (Constant.t * assumption_status) list;
  (** The constants whose label contribution was blinded, each with its
      current status, ordered by [Constant.CanOrd.compare]. The subset with
      status [Axiom] is the library's assumption set. *)
  foreign_opaque_libraries : DirPath.Set.t;
  (** The libraries, other than this one, whose opaque table this library's
      compiled form holds an [Indirect] reference into (a functor application
      or [Include] of their opaque proofs). A dependent keeps its registered
      object across an edit to such a library only when that library's object
      is byte-identical, because the blinded label no longer pins the opaque
      index the reference reads. *)
  copied_from_libraries : DirPath.Set.t;
  (** The libraries, other than this one, a declaration of this library is
      copied from: every [foreign_opaque_libraries] owner, plus the canonical
      origin ([mod_delta]) of every signature constant and inductive -- an
      [Include] or module alias keeps the origin's canonical name. A superset
      of [foreign_opaque_libraries]; an over-approximation only makes the keep
      rule more conservative (D18 S1). *)
}

val axiom_report :
  compiled:Safe_typing.compiled_library -> axiom_report
