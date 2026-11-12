(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The comparator of
    [rocqchk -compare CONFIG -challenge DIR -compare-out FILE].

    The challenge and the answer carry the same library names. [rocqchk]
    checks the answer with the kernel as it does without the option; this
    module loads the challenge into a second environment without a check,
    compares every challenge declaration with the answer declaration of the
    same canonical kernel name, computes each named theorem's axiom closure
    and writes a JSON verdict.

    The comparison is structural after a one-to-one renaming of universe
    levels: no conversion, no reduction, and no constant is unfolded.

    {2 Where a shared library may come from}

    The answer's tree may Require more of the image than the challenge
    files do, so the challenge environment loads the same SHARED libraries
    the answer loaded -- those outside the roots the challenge stands in
    for -- and a constraint one of them carries is then not read as one the
    answer invented. That rests on a shared library being something the
    answer cannot write, so the one trusted source of them is the IMAGE's
    installed load path: the corelib directory and user-contrib.

    A graded run therefore binds exactly one root with [-Q], the answer's
    project root, and leaves [ROCQPATH], [COQPATH], [-coqlib] and the XDG
    directories unset, and starts in a working directory that holds no
    [.vo] -- each of those is a load path the answer's side could otherwise
    fill. The option refuses what it can see: a bound root the challenge
    does not stand in for and whose libraries the config does not pin
    (every library of such a root must be pre-checked), any bound root
    that is empty or is one of the image's own top-level names, and, on
    either side, a library outside the challenge's roots and not
    pre-checked whose recorded file lies directly in the working directory
    or under a bound directory ([prepare]). A library that passes is shared
    by where its file is, not by who wrote it. What is left -- the
    environment the grader hands the process, and so who can write the
    image's load path -- is the grader's to get right, and
    dispatch://BET-894's R5 and R1 are where it is written down.

    The test suite stands in for the image with [ROCQPATH], because a test
    must not write into the installation it runs against. *)

type config

val read_config : string -> config
(** The config is one JSON object with the keys [theorems] (each
    [{name, permitted_axioms?}]), [permitted_axioms], [tolerated_flags]
    (each [{kind, object?}]), [rewrite_rules], [prechecked]
    ([{library, sha256}]) and [challenge_files] ([{path, sha256}]). Any
    other key, a duplicate key, a byte after the top-level value, a byte
    sequence that is not UTF-8 or a name that is not a string is an error.

    A permitted axiom is named by the name it prints, and is the task's
    declaration of that name: an axiom a theorem's proof reaches passes only
    when its name is in the theorem's permitted list AND the constant of
    that kernel name lives under a pre-checked library or a shared one (a
    library outside every root the challenge stands in for: the image's own),
    exported or a field of a sealed module it hides, or the challenge and
    the answer both export it. A module path and a library path print
    alike (the constant [g] of a module [Q] of the library [R.P] prints
    [R.P.Q.g]), so a constant that only prints a permitted name fails with
    the reason that it is not the task's declaration of that name, followed
    by where the reached object lives and why it is not the task's.

    A theorem the config names is read by the kernel name of the challenge's
    constant of that printed name (two challenge constants printing it is an
    error), and a theorem whose name two answer constants print fails.

    A tolerated flag with an [object] tolerates that kind on that object
    alone, matched by the name it prints AND, by the rule for permitted
    axioms, only when the flagged object is the task's declaration of that
    name, so a relaxed condition the standard library rests on does not
    tolerate the same condition in the agent's own declaration. Without an
    object, [indices-not-mattering] applies wherever it appears: every
    inductive of an image built without [-indices-matter] may carry it, and
    the replaced route always allows it. [uip] is allowed by that route when
    the task enables [allow_uip]; this comparator accepts a kind-only [uip]
    entry when its config requests one.

    [answer-universe-constraints] is a kind-only tolerance for the global
    universe comparison, and one that names an object is an error. It skips
    only the answer-to-challenge direction; the challenge-to-answer
    direction, declaration comparison, axiom checks and kernel checking
    still run. If that skipped direction would have failed, the record of
    every theorem the answer holds carries the flag with an object that
    summarizes the first failing constraints and their remaining count. It is
    not recorded when the direction already passes.

    Every other kind without an object is an error:
    [assumed-positive], [unsafe-fixpoint], [type-in-type] and
    [unchecked-eliminations] are how a proof of False is written, and the
    replaced route denies them by name or vouches for one object at a time.
    @raise CErrors.UserError on any of these errors. *)

val prechecked_libraries : config -> string list
(** The libraries the config declares pre-checked. They load through the
    existing [-admit] path, so the option adds each of them to the admit
    list; the config is the only place that names them.

    A pre-checked library is never a shared one: the admit list puts it in
    the ANSWER's environment whether the answer's tree Requires it or not,
    and the challenge environment takes it only through its own files'
    Require closure. A config pins bytes; it cannot add a library to the
    challenge's universe graph and so decide what the challenge stands
    on. *)

type t

val prepare :
  config -> dir:string -> out:string -> add_challenge_load_path:(unit -> unit) ->
  under_challenge_root:(Names.DirPath.t -> bool) ->
  open_roots:(Names.DirPath.t * string) list -> bound_dirs:string list -> t
(** Resolve the challenge files under [dir] and check the sha256 of each.
    [add_challenge_load_path] puts [dir] on the load path in place of the
    answer's directories; it is called once, inside the challenge load.
    [under_challenge_root] says whether a library name lives under one of
    those roots: those are the answer's own libraries. Every other library
    the answer loaded, unless pre-checked, is a shared one, which the
    challenge loads too, and the run is refused unless the file the loader
    recorded for it, on either side, lies outside every place an answer's
    file is found in: directly in the working directory, which the load
    path binds implicitly, or anywhere under one of [bound_dirs], the
    directories the command line binds (real paths, links resolved). That
    is a statement about where the file is, not about who wrote it: a file
    elsewhere is the image's only as far as the launch keeps the answer from
    writing the image's load path (above).
    [open_roots] are the bound roots the challenge does NOT stand in for,
    with the directory each is bound to; the run is refused when the answer
    loaded a library from under one of them that the config does not
    pre-check.
    @raise CErrors.UserError when a file is missing or its sha256 differs. *)

val run :
  t -> Environ.env ->
  (Opaqueproof.opaque -> Opaqueproof.opaque_proofterm) ->
  Safe_typing.safe_environment ->
  answer_deps:(Names.DirPath.t * (Names.DirPath.t * Safe_typing.vodigest) array) list ->
  unit
(** Load the challenge into an environment of its own on top of the given
    empty safe environment, compare, and write the verdict file. The
    environment is the answer's, as [rocqchk] checked it, and the accessor
    reads its opaque proofs.
    @raise CErrors.UserError when a pre-checked library's sha256 differs,
    when the two sides record different dependency digests for a pre-checked
    library, or when the config names a theorem the challenge does not hold.
    A verdict is never an error: the file is written and the run exits 0. *)

val sha256_of_file : string -> string
(** The hex SHA-256 of a file. [rocqchk -sha256 FILE] prints it, which is how
    the test suite checks this implementation against the standard vectors
    and against [sha256sum]. *)

(** {6 The comparison itself}

    Exposed in the shape [kernel/indmerge.ml] will take, so that the two can
    be merged when it lands. *)

type umap
(** A bijection between the challenge's universe levels and the answer's,
    built as the walk goes. A level that would map to two levels, or two
    levels that would map to one, is a failure. *)

type diff = string
(** What differs, and where. *)

val empty_umap : umap

val equal_constr : umap -> Constr.t -> Constr.t -> (umap, diff) result

val eq_mib :
  umap -> Environ.env -> Declarations.mutual_inductive_body ->
  Declarations.mutual_inductive_body -> (umap, diff) result
