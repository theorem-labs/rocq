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
    levels, of global sort qualities and of functor parameters, which each
    side numbers in the order it declares them: no conversion, no
    reduction, and no constant is unfolded. A global level or quality that
    only the constraints of a polymorphic context name is renamed by the
    one solution constraint that fits it. When nothing else decides, a tie
    renames it to the solution's level or quality of the same library and
    number: first the one among several solution constraints that fit, and
    only when no constraint takes such a tie, for a constraint between two
    such levels or qualities, both ends at once when the solution holds
    that same constraint. The first tie of a declaration waits for the other
    declarations to decide what they can; its later ties do not, which can
    refuse an honest solution, never pass a wrong one. Nothing is searched
    beyond the tie, so a solution that numbers such levels otherwise, as
    when it declares more global levels before them or declares them in
    another order, can make the declaration differ though it is honest, in
    two ways. When several of its constraints fit and none of them has the
    number of the challenge's level, the declaration differs as undecided,
    the reason naming that level: with [Universe u w.] in the challenge,
    [Universe spare1 spare2 u w.] in the solution and
    [small@{i | i < u, i < w}] on both sides, each constraint of [small]
    fits two of the solution's, and neither of them has the number of the
    challenge's level. When one that fits has that number but is not the
    level that stands for the challenge's, the tie pairs the wrong level,
    and the declaration differs as having other constraints, with no level
    named: with [Universe x x2 y y2.] in the challenge,
    [Universe x x2 y2 y.] in the solution and
    [pick@{i j | j < x, j < x2, x < y, i < y, i < y2}] on both sides, the
    tie on [i < y] renames the challenge's [y] to the solution's [y2], and
    [x < y] then stands for [x < y2], which the solution does not hold.

    A challenge constant without a body (an axiom, a parameter or an
    admitted proof, which a [.vo] file does not tell apart) may be given one
    by the solution only when the challenge states it as a proposition or
    the config names it as a theorem. That body must be opaque when another
    compared challenge declaration names the constant in what the
    comparison reads of it (the type or transparent body of a constant, the
    parameters, arities, constructor types or projection types of an
    inductive block, or any field of a module type, the types of its
    functor parameters included), unless the challenge states it as data: a
    transparent proof would unfold there and change what that declaration
    states. So a function that the config names and that a lemma of the
    challenge specifies may be transparent: the lemma is stated about the
    function the solution chooses. What the challenge states a constant to
    be is read from the sort of the type it states for it, typed in the
    challenge environment and not reduced. In [Prop] or [SProp], the
    constant is a proposition. In [Set] or [Type], it is data, even when
    its type unfolds to a proposition: a challenge that wants a lemma kept
    opaque states it in [Prop]. In a sort variable or a global sort, or
    when the type cannot be typed there, the run cannot tell, and each rule
    refuses: such a constant may be given a body only when the config names
    it, and only an opaque one when another declaration names it. A
    sort-polymorphic constant is a proof at an instance in [Prop], and a
    global sort, which a library declares, may be meant for propositions.
    The type of a field of a module type may name the other fields of the
    module type and the functor parameters, which no environment holds, so
    such a field that the challenge leaves without a body may not be given
    one, whatever its type. A difference in a module type names the fields
    and functor parameters it lies in.

    A challenge constant that the kernel registers as a primitive type
    ([Primitive int := #int63_type]) differs from a solution constant that
    it registers as another one or as none, and the other way round: the
    literals of a primitive type have its constant for type, so a parameter
    that the solution registered as one would be inhabited.

    {2 Where a shared library may come from}

    The solution's tree may Require more of the installation than the
    challenge files do, so the challenge environment loads the same SHARED
    libraries the solution loaded -- those outside the root the challenge
    stands in for that the config does not pre-check -- and a constraint one
    of them carries is then not read as one the solution invented. That
    rests on a shared library being something the solution cannot write, so
    a run accepts one only from a TRUSTED directory ([run]'s [trusted]): the
    real path of the directory its file was found in must lie under the
    real path of the corelib directory, of user-contrib (both as [-coqlib]
    or [ROCQLIB] select them) or of a directory that [ROCQPATH] or
    [COQPATH] lists. Whoever starts the run chooses those directories, and
    keeping them out of the solution's reach is theirs to get right. The
    load path stores each directory with links resolved, so a file link in
    a trusted directory is taken as the directory's, and a directory link
    is not: a library found below one is refused unless the link's target
    lies under a trusted directory too.

    Every other directory the load path binds is refused for a shared
    library unless a trusted directory holds it: the XDG directories (the
    [coq] directory of [XDG_DATA_HOME], by default
    [$HOME/.local/share/coq], and of each directory of [XDG_DATA_DIRS]),
    which the load path searches before corelib and user-contrib. The
    working directory, which the load path binds implicitly, and every
    directory that [-Q] or [-R] binds are refused for a shared library even
    then ([run]). A run is meant to bind one root with [-Q], the solution's
    project root: [check_roots] refuses the empty root and a root that the
    default load path serves, and [run] refuses the libraries named for
    checking when they lie under no bound root or under more than one. A
    library that passes is shared by where its file is, not by who wrote
    it. *)

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
    compared in both directions too, through the renaming of qualities, and
    with no exception in the solution-to-challenge direction: every
    constraint the solution's graph holds between two qualities that are
    constants or that the renaming pairs with the challenge's must hold in
    the challenge, whichever library declares them, since a library may add
    a constraint on the sort of another, an installed or pre-checked one
    included. The renaming pairs with itself each level and sort that both
    sides hold of a pre-checked library, of an installed one and of a
    library that a pre-checked one rests on, so a constraint on such a sort
    counts even when no compared declaration names it. A sort that only the
    solution declares, and a constraint on it, count only where a path
    through it joins two such qualities.

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

val check_prechecked : config -> Names.DirPath.t list
(** [check_prechecked cfg] refuses a pre-checked library whose file, the one
    the load path in place resolves its name to
    ([CheckLibrary.library_file]), does not have the sha256 that the config
    gives, then returns the libraries the config declares pre-checked. A
    pre-checked library loads without a check, and [rocqchk] calls this
    before it reads any library, so no pre-checked library loads without a
    check from bytes the config does not pin. They load through the
    existing [-admit] path, so the option adds each of the returned
    libraries to the admit list; the config is the only place that names
    them. When the command line names a file of such a library in a second
    directory bound to its logical path, the loader reads that file
    instead, so [run] checks the pin on that file as well.

    A pre-checked library is never a shared one: the admit list puts it in
    the SOLUTION's environment whether the solution's tree Requires it or
    not, and the challenge environment never takes it as a shared library.
    A config pins bytes; it cannot add a library to the challenge's universe
    graph and so decide what the challenge stands on.
    @raise CErrors.UserError on the first library whose sha256 differs, or
    on one that the load path does not find. *)

val check_roots : default_roots:Names.Id.t list -> (string * Names.DirPath.t) list -> unit
(** [check_roots ~default_roots roots] refuses a [-Q] or [-R] root
    [(directory, logical root)] of [roots] that binds the empty root or one
    of [default_roots], the top-level names that the default load path (the
    corelib directory, user-contrib, the XDG directories and ROCQPATH)
    serves without a [-Q]. It reads nothing but its arguments, so [rocqchk]
    calls it as soon as the load path is set up.
    @raise CErrors.UserError on the first such root. *)

val run :
  config -> dir:string -> out:string -> roots:(string * Names.DirPath.t) list ->
  trusted:string list -> checked:Names.DirPath.t list -> admitted:Names.DirPath.t list ->
  add_load_path:(unix_path:string -> rocq_root:Names.DirPath.t -> unit) ->
  Environ.env -> Safe_typing.safe_environment -> unit
(** [run cfg ~dir ~out ~roots ~trusted ~checked ~admitted ~add_load_path env
    senv] compares the solution with the challenge of the directory [dir]
    and writes the verdict to the file [out]. [env] is the solution's
    environment, as [rocqchk] checked it, whose opaque proofs are read from
    the library tables in place ([CheckLibrary.indirect_accessor]); the
    challenge is loaded into an environment of its own on top of [senv], an
    empty safe environment.

    [roots] are the [-Q] and [-R] roots, each [(directory, logical root)];
    [trusted] are the trusted directories (above), each with its
    subdirectories: the corelib directory, user-contrib and the directories
    of [ROCQPATH] and [COQPATH], none with [-boot]; [checked] are the
    libraries the command line names for checking, with or without
    [-norec], and [admitted] those it gives with [-admit] (not the
    pre-checked libraries the option adds to the admit list), each by the
    library name the loader gave it. The challenge stands in for the root of
    [roots] that the libraries of [checked] live under:
    [add_load_path ~unix_path ~rocq_root] binds [unix_path] and its
    subdirectories to [rocq_root], as [-Q] does, and is called once, with
    [dir] and that root, so that the challenge load finds [dir] in front of
    the solution's directories. A library under that root is the solution's
    own. Every other library the solution loaded, unless pre-checked, is a
    shared one, which the challenge loads too, from the same file (above).
    The challenge load validates every library it reads, as
    [rocqchk -compare] validates the solution's: the load path may find a
    file the solution's side wrote, which a refusal below rejects only once
    it is read.

    A library is pinned by its sha256 when the file the solution loaded for
    it has the sha256 the config gives for it: in [prechecked], or in
    [challenge_files] for its file in [dir], the file at the path that its
    own file has below the directory of the root the challenge stands in
    for (real paths, so a config path may use [/] on every platform).

    The verdict's last key, [admitted], lists the libraries of [admitted] by
    logical name, in their order and each once.

    A verdict is never an error: the file is written whatever it says, and
    [rocqchk] then exits 0 unless [-axiom-free] fails, as it does without
    the option. The verdict is written to a temporary file next to it and
    renamed, so a write that fails leaves no verdict file and exits
    non-zero.

    The run is refused, and writes no verdict, when:
    - the libraries of [checked] lie under no root of [roots], or under
      more than one;
    - a challenge file is missing or its sha256 differs;
    - the file the solution loaded a pre-checked library from does not have
      the sha256 the config pins for it, which can be another file than the
      one [check_prechecked] hashed (above);
    - the solution loaded a library from under a root of [roots] that the
      challenge does not stand in for and the config does not pre-check;
    - the solution loaded a library that is neither under the root the
      challenge stands in for nor pre-checked from a file directly in the
      working directory, which the load path binds implicitly, or anywhere
      under a directory of [roots] (real paths, links resolved), or from a
      directory under none of [trusted] (real paths);
    - a pre-checked library rests, directly or not, on a library that is
      neither pre-checked, pinned by its sha256, nor shared: the digest a
      pre-checked library records for it is the one the dependency's own
      file states, which pins nothing, and a kernel check of it is not
      enough, since the pre-checked library was not checked against it;
    - the solution loaded a library under the root the challenge stands in
      for without a check ([CheckLibrary.unchecked]: a dependency of a
      [-norec] or [-admit] library), which is then neither checked nor,
      unless the challenge files Require it, compared, and that library is
      neither pre-checked, pinned by its sha256, nor in [admitted]: a
      library one of [admitted] depends on is not exempt;
    - the challenge loaded a library that is under the root it stands in
      for and not pre-checked from a file that is not under [dir] (real
      paths, links resolved), as when [dir] lacks a library and the load
      path finds the solution's;
    - the challenge loaded a library that is neither under that root nor
      pre-checked from a file in the working directory, under a directory
      of [roots] or in a directory under none of [trusted];
    - a challenge library and its solution library record different
      dependency digests for a pre-checked or shared library;
    - the challenge loaded a pre-checked library, or a shared one that the
      solution loaded too, from another file than the solution's (real
      paths), as when a directory link in [dir] takes the binding of a
      directory the load path binds and the name resolves to another file,
      unless the library is pre-checked and that file has the sha256 the
      config pins for it;
    - the config names a theorem the challenge does not hold, or one whose
      name two constants of the challenge print;
    - a theorem's axiom closure reaches an axiom or a flag's object whose
      printed name is not made of identifiers, or an inductive type whose
      name is not an identifier.
    @raise CErrors.UserError on each refusal above. *)

val sha256_of_file : string -> string
(** The SHA-256 of a file's bytes as 64 lowercase hexadecimal digits
    ({!CSha256.file}), the digest a config gives. [rocqchk -sha256 FILE]
    prints it.
    @raise CErrors.UserError when the file cannot be read. *)
