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

    The challenge and the solution carry the same library names. [rocqchk]
    checks the solution with the kernel as it does without the option; this
    module loads the challenge into a second environment without a check,
    compares every challenge declaration with the solution declaration of
    the same user kernel name, computes each named theorem's axiom closure
    and writes a JSON verdict.

    The comparison is structural after a one-to-one renaming of universe
    levels: no conversion, no reduction, and no constant is unfolded.

    {2 Where a shared library may come from}

    The solution's tree may Require more of the installation than the
    challenge files do, so the challenge environment loads the same SHARED
    libraries the solution loaded -- those outside the roots the challenge
    stands in for -- and a constraint one of them carries is then not read
    as one the solution invented. That rests on a shared library being
    something the solution cannot write, so the one trusted source of them
    is the installed load path: the corelib directory and user-contrib.

    A run therefore binds exactly one root with [-Q], the solution's
    project root, and leaves [ROCQPATH], [COQPATH], [-coqlib] and the XDG
    directories unset, and starts in a working directory that holds no
    [.vo] -- each of those is a load path the solution's side could
    otherwise fill. The option refuses what it can see: a bound root the
    challenge does not stand in for and whose libraries the config does not
    pin (every library of such a root must be pre-checked), any bound root
    that is empty or is one of the installed load path's own top-level
    names, and, on either side, a library outside the challenge's roots and
    not pre-checked whose recorded file lies directly in the working
    directory or under a bound directory ([check_roots], [run]). A library
    that passes is shared by where its file is, not by who wrote it. What is
    left -- the environment the process is started in, and so who can write
    the installed load path -- is for whoever starts the run to get right. *)

type config

val read_config : string -> config
(** The config is one JSON object with the keys [theorems] (each
    [{name, permitted_axioms?}]), [permitted_axioms], [tolerated_flags]
    (each [{kind, object?}]), [rewrite_rules], [prechecked]
    ([{library, sha256}]) and [challenge_files] ([{path, sha256}]). Any
    other key, a duplicate key, a byte after the top-level value, a byte
    sequence that is not UTF-8, a name that is not a string, or a
    pre-checked library that is not a logical name (identifiers separated
    by dots, with no [.vo]) is an error.

    A permitted axiom is named by the name it prints, and is the challenge's
    declaration of that name: an axiom a theorem's proof reaches passes only
    when its name is in the theorem's permitted list AND the constant of
    that kernel name lives under a pre-checked library or a shared one (a
    library outside every root the challenge stands in for: an installed
    one), exported or a field of a sealed module it hides, or the
    challenge and the solution both export it. A module path and a library
    path print alike (the constant [g] of a module [Q] of the library [R.P]
    prints [R.P.Q.g]), so a constant that only prints a permitted name fails
    with the reason that it is not the challenge's declaration of that name,
    followed by where the reached object lives and why it is not the
    challenge's.

    A theorem the config names is read by the kernel name of the challenge's
    constant of that printed name (two challenge constants printing it is an
    error), and a theorem whose name two solution constants print fails.

    A tolerated flag with an [object] tolerates that kind on that object
    alone, matched by the name it prints AND, by the rule for permitted
    axioms, only when the flagged object is the challenge's declaration of
    that name, so a relaxed condition the standard library rests on does not
    tolerate the same condition in the solution's own declaration.
    [indices-not-mattering] and [uip] take both forms. Without an object,
    [indices-not-mattering] applies wherever it appears: indices not
    mattering is Rocq's default, so every inductive of an installation built
    without [-indices-matter] may carry it. The config has no [allow_uip]
    input, so a kind-only [uip] entry is that switch: writing it says that
    definitional UIP is allowed wherever a proof reaches it. A [uip] entry
    with an object allows it on that object alone, when the object is the
    challenge's declaration, and leaving both out says that it is not
    allowed.

    [rewrite_rules] (default [false]) is whether the solution may declare a
    rewrite rule. Without it, every theorem fails when a library the
    solution loaded declares one, whatever symbol it rewrites: each library
    except a pre-checked one and a shared one. A library only the solution
    has counts, and so does a rule inside a module whose signature hides it,
    and a rule a module type or a module's signature declares. A rule the
    challenge declares counts too, since the solution's copy of it declares
    it again: such a challenge needs the option. A [Symbol] declaration with
    no rule is not a rule: it is an assumption, and the closure reports it
    among the theorem's axioms like an [Axiom], so a theorem whose proof
    reaches a symbol fails unless the config permits that symbol by name,
    under the rule for permitted axioms (a symbol the solution itself
    declares is never the challenge's).

    The universe graphs of the two sides are compared in both directions:
    every constraint of the challenge must hold in the solution, and every
    constraint the solution adds that reaches a level of the challenge's
    own must hold in the challenge; a failing direction fails every
    theorem. The elimination constraints between sort qualities (a global
    sort a library declares, and constraints such as [s -> Prop] on it) are
    compared in both directions too, the qualities by identity, and with no
    exception in the solution-to-challenge direction: every constraint the
    solution's graph holds between two qualities the challenge's graph holds
    must hold in the challenge, whichever library declares them, since a
    library may add a constraint on the sort of another, an installed or
    pre-checked one included.

    [answer-universe-constraints] is a kind-only tolerance for the global
    universe comparison, and one that names an object is an error. It skips
    only the solution-to-challenge direction of the universe graphs; the
    challenge-to-solution direction, both directions of the elimination
    constraints (which stay strict), declaration comparison, axiom checks
    and kernel checking still run. If that skipped direction would have
    failed, the record of every theorem the solution holds carries the flag
    with an object that summarizes the first failing constraints and their
    remaining count. It is not recorded when the direction already passes.

    [assumed-positive], [unsafe-fixpoint] and [type-in-type] are an error
    with an object or without: each is a way to prove [False] (a negative
    inductive type, a fixpoint that does not terminate, Girard's paradox),
    whatever the object. [unchecked-eliminations] without an object is an
    error: it is a way to prove [False] too (an elimination the check would
    refuse), so the config may tolerate it only on an object it names, one
    declaration at a time. Any other kind without an object is an error as
    well.
    @raise CErrors.UserError on any of these errors. *)

val prechecked_libraries : config -> Names.DirPath.t list
(** The libraries the config declares pre-checked. They load through the
    existing [-admit] path, so the option adds each of them to the admit
    list; the config is the only place that names them.

    A pre-checked library is never a shared one: the admit list puts it in
    the SOLUTION's environment whether the solution's tree Requires it or
    not, and the challenge environment takes it only through its own files'
    Require closure. A config pins bytes; it cannot add a library to the
    challenge's universe graph and so decide what the challenge stands
    on. *)

val check_roots : installed_roots:string list -> (string * Names.DirPath.t) list -> unit
(** [check_roots ~installed_roots roots] refuses a [-Q] or [-R] root
    [(directory, logical root)] of [roots] that binds the empty root or one
    of [installed_roots], the top-level names that the installed load path
    serves without a [-Q] (above). It reads nothing but its arguments, so
    [rocqchk] calls it as soon as the load path is set up.
    @raise CErrors.UserError on the first such root. *)

val run :
  config -> dir:string -> out:string -> roots:(string * Names.DirPath.t) list ->
  checked:Names.DirPath.t list -> admitted:Names.DirPath.t list ->
  add_load_path:(unix_path:string -> rocq_root:Names.DirPath.t -> unit) ->
  Environ.env -> Safe_typing.safe_environment -> unit
(** [run cfg ~dir ~out ~roots ~checked ~admitted ~add_load_path env senv]
    compares the solution with the challenge of the directory [dir] and
    writes the verdict to the file [out]. [env] is the solution's
    environment, as [rocqchk] checked it, whose opaque proofs are read from
    the library tables in place ([CheckLibrary.indirect_accessor]); the
    challenge is loaded into an environment of its own on top of [senv], an
    empty safe environment.

    [roots] are the [-Q] and [-R] roots, each [(directory, logical root)];
    [checked] are the libraries the command line names for checking, with or
    without [-norec], and [admitted] those it gives with [-admit] (not the
    pre-checked libraries the option adds to the admit list), each by the
    library name the loader gave it. The challenge stands in for each
    root of [roots] that a library of [checked] lives under:
    [add_load_path ~unix_path ~rocq_root] binds [unix_path] and its
    subdirectories to [rocq_root], as [-Q] does, and is called with [dir]
    for each such root, once, so that the challenge load finds [dir] in
    front of the solution's directories. A library under such a root is the
    solution's own. Every other library the solution loaded, unless
    pre-checked, is a shared one, which the challenge loads too (above).

    A library is pinned by its sha256 when the file the solution loaded for
    it has the sha256 the config gives for it: in [prechecked], or in
    [challenge_files] for its file in [dir], the file at the path that its
    own file has below the directory of its root, a root the challenge
    stands in for. A library that a pre-checked one depends on, directly or
    not, must be pre-checked too, pinned by its sha256, or shared: the
    digest a pre-checked library records for it is the one the dependency's
    own file states, which pins nothing, and a kernel check of it is not
    enough, since the pre-checked library was not checked against it. A
    library the solution loaded without a check ([CheckLibrary.unchecked]: a
    dependency of a [-norec] or [-admit] library) is neither checked nor,
    unless the challenge files Require it, compared, so under a root the
    challenge stands in for it must be pre-checked, pinned by its sha256, or
    in [admitted] itself: a library one of [admitted] depends on is not
    exempt.

    The verdict's last key, [admitted], lists the libraries of [admitted] by
    logical name, in their order and each once.

    A verdict is never an error: the file is written and the run exits 0.
    The verdict is written to a temporary file next to it and renamed, so a
    write that fails leaves no verdict file and exits non-zero.
    @raise CErrors.UserError when a challenge file is missing or its sha256
    differs; when the solution loaded a library from under a root of
    [roots] that the challenge does not stand in for and the config does not
    pre-check; when a pre-checked library's sha256 differs; when the
    solution loaded a library that is neither under a root the challenge
    stands in for nor pre-checked from a file directly in the working
    directory, which the load path binds implicitly, or anywhere under a
    directory of [roots] (real paths, links resolved); when a pre-checked
    library rests on a library that is neither pre-checked, pinned by its
    sha256, nor shared; when the solution loaded a library under a root the
    challenge stands in for without a check and that library is neither
    pre-checked, pinned by its sha256, nor in [admitted]; when the challenge
    loaded a library that is under its roots and not pre-checked from a file
    that is not under [dir] (real paths, links resolved), as when [dir] lacks
    a library and the load path finds the solution's; when the challenge
    loaded a library that is neither under its roots nor pre-checked from a
    file in the working directory or under a directory of [roots]; when a
    challenge library and its solution library record different dependency
    digests for a pre-checked or shared library; when the config names a
    theorem the challenge does not hold, or one whose name two constants of
    the challenge print; or when a theorem's axiom closure reaches an axiom
    or a flag's object whose printed name is not made of identifiers, or an
    inductive type whose name is not an identifier. *)

val sha256_of_file : string -> string
(** The SHA-256 of a file's bytes as 64 lowercase hexadecimal digits
    ({!CSha256.file}), the digest a config gives. [rocqchk -sha256 FILE]
    prints it.
    @raise CErrors.UserError when the file cannot be read. *)
