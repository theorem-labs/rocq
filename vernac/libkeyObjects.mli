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
      [Key_as_is], or its copy through the stripper of its kind
      ([Key_stripped]), which erases what the key must not read. The
      container entries hold no source location and are kept as they are.
      An ML-MODULE object and the [ATTEMPTS] object ([Attempts]) have their
      plugin file digests erased: see the version-4 paragraph below;
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

    {b Plugin files out of the key (version 4, BET-342).} A [Declare ML
    Module] contributes the plugin names, each with whether it is an
    implicit dependency (the ML-MODULE object), and the files findlib
    resolved it to (an [ATTEMPTS] record of a rolled-back one), not the
    [Digest.file] or SHA-256 of those files, which both objects still store.
    A plugin's [.cmxs] is rebuilt by any change to the OCaml code it is
    compiled against: between two builds of this fork whose [plugins/] trees
    are identical, 26 of 27 installed [.cmxs] files differ, so a key that
    read those digests moved for every library that declares a plugin and,
    through the dependency digests, for every library above it (BET-342,
    measured: 1 of 691 Corelib, Ltac2 and Stdlib labels equal across one such
    move; with version 4, 691 of 691).

    What this costs. A dependent loads a plugin by name, whatever file
    findlib finds then ([Mltop.load_ml_objects]; the stored digests are
    written and never read back), so the digests never decided what a
    dependent loads. What they did was move the label of a declaring library
    whenever the plugin's file moved, which carried a plugin's own change to
    the dependents (upstream 67ac9e9d36, "Put back digests in mltop", fixing
    rocq-prover/rocq#15649). Version 4 drops that carrier, and what it rests
    on instead is an obligation on the build: {e a change to the
    representation of a value a [.vo] stores -- a kernel value or a plugin's
    marshalled object -- bumps [Coq_config.vo_version], and one value of
    that number names one representation across every build whose files can
    meet}, the second half because two branches cut from one base can each
    bump to the same number for different representations. The number is in
    [Libkey]'s header and so in every label. [rocqchk] is not exposed either
    way: it reads both object segments as [Any]; what the obligation
    protects is the [coqc] that reads an older build's objects.

    The obligation is checked, as far as a build can check it, by
    test-suite/misc/vo-format.sh, which pins five things against that
    version: the structure of a [.vo]'s segments as checker/values.ml
    describes them, the names of the registered object kinds, the OCaml
    type of the payload each of those kinds stores (with the definition of
    every type that type reaches, read from the typed trees the build
    writes, checker/vo_payloads.ml), which of the four types of
    [Goptions.option_kind] each declared option stores, and the element
    type of each [Goptions] table. A kind only the new build has passes
    there: a build that does not know a kind refuses the file instead of
    misreading it.

    What that payload printing does not reach it names rather than drops,
    and the head of checker/vo_payloads.ml is the one place that list is
    written down. In short: a type no typed tree defines (a functor's
    result, a functor argument's type, a type of another package), and a
    type variable no declaration binds.

    What no part of the printing reaches, and the reader of this label
    must carry itself:
    - the value behind a [Dyn] tag, so a stored Ltac expression is pinned
      down to its generic arguments and no further;
    - the structure of the [vm] segment, which this fork's rocqchk
      regenerates and never reads, so nothing checks that description
      against what the kernel writes (the payload part does print the
      types of that segment, but only because the [REQUIRE] kind's payload
      reaches them, and that kind is never written to a file);
    - the meaning of a string, the bytecode of that segment among them,
      and the order of a type's constant constructors in the segment
      structure (the payload types do print them in order);
    - a plugin that is not Rocq's own, whose authors cannot bump Rocq's
      number at all, so a reader that keeps objects across two builds must
      require the same versions of the packages that install those
      plugins;
    - the choice of a number no other branch used.

    The other thing a plugin rebuild changes -- how the
    elaboration of a file that uses its objects goes -- is a property of
    the build that compiles that file, not of this library.

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
}

val axiom_report :
  compiled:Safe_typing.compiled_library -> axiom_report
