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

    {b Byte layout, version 6.} The label is
    {v Libkey.label (Obj.repr (version, vmlibrary_format_version, compiled, syn', obj', summary')) v}
    (32 bytes) where:
    - [vmlibrary_format_version] is the format version of the VM-bytecode
      segment this build reads and writes: see the version-6 paragraph
      below;
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

    {b The axiom-or-opaque-proof blinding (version 3, S1b; restricted in
    version 5, D18 F1).} A constant of the library's own signature (its
    structure and, recursively, the signature of each of its submodules:
    exactly the constants [axiom_report] lists) whose body is [Undef None]
    (an axiom or parameter with no body, as [Admitted] and [Axiom] make) and
    one whose body is [OpaqueDef _] (an opaque proof, as [Qed] makes) give
    the {e same} label contribution: the label reads their type, universe
    context and constraints, typing and guard flags, section data, relevance
    and inline mark, but not the axiom-or-opaque distinction nor the opaque
    table index ([blind_constant]). [Admitted -> Qed] and [Qed -> Admitted]
    of such a constant therefore keep the label. A transparent body ([Def]),
    which conversion unfolds, is {e not} blinded, and neither is an
    inlinable parameter ([Undef (Some _)]), whose inline level a functor
    application observes. The blinding is sound because a dependent never
    observes the erased difference (kernel/environ.ml:654-677,
    vmbytegen.ml:988-990, genlambda.ml:797-798) except through what the keep
    rule reads beside the label: the opacity a dependent's non-opaque
    strategy command or extraction saw ([KeepFacts], compared with the status
    [axiom_report] gives now); the opaque proof BODIES an extraction with
    AccessOpaque (the default) read, which it logs as [opaque = true] queries
    naming the library that holds the constant read and the library whose
    opaque table holds the body read; the library's assumption set (its
    monotone axiom condition, over the closures [keepfacts] stores, whose
    walk logs each body of the library's own copy it reads from another
    library's table as the same kind of query); and which opaque proof a
    foreign [Indirect] reference resolves to (its foreign-opaque-reference
    check: the referenced library's object byte-identical). For a copy a
    module operation did not strengthen (a functor application, an
    [Include] of one, a sealed [Module X : T := L.F A] an extraction or the
    closure walk reads from its expression) the holder and the table can
    differ, however many copies away the proof came from, so a body read
    records both and the keep rule keeps the dependent only when both
    libraries' objects are byte-identical. [foreign_opaque_libraries]
    does not cover body reads. The status comparison and the assumption set
    read a constant's status off [axiom_report], so the blinding covers only
    the constants it lists; a body read reads no status, its check being
    byte-identity. Every other constant the compiled form holds -- in a
    functor's body, in a functor parameter's module type, in a module type,
    in the implementation of a sealed module -- keeps an opaque proof
    distinct from an axiom, read as one fixed opaque body with no table
    index: a functor application, [Declare Module M : T] or [Module X : T :=
    ...] copies such a form into the dependent's own declarations, where it
    decides whether the dependent compiles ([Transparent R.c]) and what its
    [Print Assumptions] says (review gate 1, F1). So an [Admitted -> Qed]
    edit there moves the label, and a shift of the opaque table index alone
    does not.

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
    misreading it. A segment only the new build writes needs no new version
    either, but must be recorded: this rests on the assumption that every
    reader looks a segment up by name ([ObjFile.marshal_in_segment]), so an
    older build never reads a segment it does not know, and a newer build
    treats one a file lacks as absent. The one such segment is [keepfacts]
    ([KeepFacts]), which [rocqchk] never reads and [coqc] reads (a
    dependency's stored closures) and writes only under
    [-location-free-label]. The obligation above is on a RELEASED
    representation: [keepfacts], which no released build has written,
    changed its query shape (a table field) with no new version, and a file
    of the older shape stays safe to read, since [coqc] takes only its
    [assumptions], whose shape did not change, and rocq-library-label
    validates the segment before it reads the queries.

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
    - the OCaml type of the [keepfacts] segment ([KeepFacts.t]): the
      printing gives checker/values.ml's description of it ([v_keepfacts]),
      not the type [coqc] marshals. What ties the two is that
      rocq-library-label validates every keepfacts segment it reads against
      that description, as rocqchk validates the segments it reads, and reads
      one that does not match as absent, and misc/library-label-keepfacts.sh
      reads this build's own segments through it: a change to [KeepFacts.t]
      without the matching change to the description fails that test, and
      one with it fails vo-format.sh. Validation checks the shape of the
      value (blocks, tags, sizes, strings), not every type change: a [bool]
      read where an [int] was written passes it;
    - the meaning of a string, the bytecode of the [vm] segment among them,
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

    {b The VM segment's format version in the key (version 6, speed-8).}
    The [vmlibrary] segment of a [.vo] holds VM bytecode: instruction words
    the C interpreter of the READING process dispatches on. A process whose
    VM lacks the opcodes the writer emitted jumps where its own table sends
    that word and dies with no message, which is why that segment carries a
    format version of its own ([Vmlibrary.format_version],
    kernel/vmlibrary.ml: a 32-bit word the segment starts with, checked
    before anything in it is unmarshalled). Two builds whose VM segments are
    in different formats cannot read each other's files, so they must never
    agree on a label, however identical a library's source, objects and
    summary are: nothing else in the key moves with that format, since the
    compiled form the label reads is the kernel value, not the bytes of the
    segment. The key therefore carries [vmlibrary_format_version], the
    number that names this build's format: 0 for a segment that starts
    straight with the marshalled table, which is what a build without the
    VM member writes, and otherwise the version word the segment starts
    with, which counts from 1. The two formats that exist are therefore 0
    and 1, and they are two labels.

    It is a number here rather than [Vmlibrary.format_version] itself
    because the branch that writes the version word and the branch that
    computes this key meet only in a release: neither is an ancestor of the
    other, so this file cannot name a value the other defines, and a build
    of this branch alone has none. The merge of the two therefore defines
    this constant as [Vmlibrary.format_version], which is one edit and
    leaves one number to raise afterwards. It is not left to a reader of
    this comment:
    test-suite/misc/library-label-vmlibrary.sh reads the first word of the
    [vmlibrary] segment of a library the build under test wrote and fails
    unless this constant names that format -- equal to the word when there
    is one, 0 when the segment starts with the marshaller's magic. A merge
    that forgets the edit fails that test, which names it, and so does a
    build whose [Vmlibrary.format_version] was raised without the key. Once
    the two branches share a base, the binding is the only definition and
    that test's purpose is gone.

    {b What the label does not cover.} The [opaques] segment (the proof
    terms of opaque constants: a changed proof keeps the label unless it
    changes what the compiled form holds, which is the point of the
    design, so its owning library must still reach the proof checker), the
    [vm] segment's bytes, which the checker regenerates (its format version
    is covered: the paragraph above), the [keepfacts] segment
    ([KeepFacts]: per-declaration assumption closures and the opacities
    commands saw, which [coqc] writes only under [-location-free-label] and
    only for a [.vo], which [rocqchk] never reads, which a dependent's [coqc]
    reads to take the closures of this library's constants instead of
    walking them, and which the keep rule reads off the CURRENT object, so it
    needs no digest; were it covered, an [Admitted -> Qed] edit would move the
    label),
    and the native sidecar files beside the [.vo]. A [.vos] built from a
    source has the same summary and [library] segments as its [.vo], and so
    the same label.
    The OCaml version is in [Libkey]'s header, so it is covered for a file
    whose stored digest has been checked against a label recomputed by a
    tool of the same build, not for one read as it is. The keep rule that
    reads labels handles all of these. *)

val version : int

val vmlibrary_format_version : int
(** The number that names the format of the [vmlibrary] segment this build
    reads and writes: [Vmlibrary.format_version] in a build that writes a
    version word, 0 in a build that writes none (the version-6 paragraph
    above). [rocq-library-label --vmlibrary-format-version] prints it. *)

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
(** The compiled library as the label reads it: every constant of its own
    signature (the ones [axiom_report] lists) with an [OpaqueDef] or [Undef
    None] body replaced by a canonical [Undef None] ([blind_constant]), and
    every other [OpaqueDef] in it by one fixed opaque body with no table
    index. Idempotent. A view for computing the label; the kernel never loads
    this. *)

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
      compiled form holds an [Indirect] reference into: copies of their
      opaque proofs that a module operation did not strengthen. It is
      computed from every constant ([foreign_opaque_of]), so it does not
      depend on which operations those are. A dependent keeps its registered
      object across an edit to such a library only when that library's object
      is byte-identical, because the blinded label no longer pins the opaque
      index the reference reads. It does not cover the tables a body read
      reads: a module whose implementation is an algebraic expression holds
      no reference, and an extraction or the walk that computes the
      library's closures reads its constants from that expression; each such
      read records its table ([KeepFacts.query]). *)
}

val axiom_report :
  compiled:Safe_typing.compiled_library -> axiom_report
