(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Treating two matching copies of an inductive type as one type.

    Off by default; turned on by [-merge-inductives] on [rocq c] and on
    [rocqchk]. With it on, when a compiled library is imported, each of its
    top-level mutual inductive blocks is compared with the blocks already in
    the environment. A block that matches an already-loaded one is given that
    one's {e canonical} name, exactly as [Module M := N] gives [M]'s
    inductives [N]'s canonical names, so every comparison site in the kernel
    -- all of which compare inductive names by [Ind.CanOrd] -- sees the two
    copies as one type. No comparison site changes.

    The renaming uses the existing module substitution machinery: a delta
    resolver rooted at the library's module path maps each matched inductive's
    kernel name to the canonical name of the already-loaded copy, and
    [Mod_declarations.subst_module] rewrites the loaded structure with it.

    Nothing a process writes carries a name only a merge justifies: every
    merge this process made is undone again in [Safe_typing.export] and on the
    opaque proof table, so a [.vo] is the same whether or not the option was
    on, and a reader must earn the merge for itself. *)

(** {6 The option} *)

val set_enabled : bool -> unit
val enabled : unit -> bool

val set_verbose : bool -> unit
(** Print one line per merge. *)

(** {6 Comparing two blocks}

    This is the part the Rocq comparator (dispatch://BET-894) calls. *)

type umap
(** A bijection between universe levels, built while the two terms are walked
    in parallel and threaded from one call to the next. A level that would
    have to map to two different levels is a failure, in both directions. *)

type diff
(** The first difference found. *)

val empty_umap : umap

val pr_diff : diff -> Pp.t

val umap_pairs : umap -> (Univ.Level.t * Univ.Level.t) list
(** The pairs of the bijection whose two sides differ, left side first. A
    caller that intends to {e equate} these levels must decide for itself
    whether it may: see [merge], which refuses a pair unless the left level
    belongs to the library being loaded and the right one does not, and
    which compares every constraint mentioning a paired level. *)

val equal_constr : umap -> Constr.t -> Constr.t -> (umap, diff) result
(** Purely structural equality, modulo the universe bijection and modulo
    nothing else: no beta, iota, zeta, eta or delta, and no conversion.
    Global names are compared by their canonical form ([Constant.CanOrd],
    [Ind.CanOrd], [Construct.CanOrd], [Projection.CanOrd]), so a caller that
    wants two {e copies} compared must have renamed one side first -- which is
    what [merge] does before it calls this.

    There is deliberately no delta here. This module implements no
    conversion-based comparison at all; the only reduction in the whole
    feature is the kernel's own conversion, which runs later, when the
    checker file's two statement types are compared. *)

val eq_mib : umap -> Environ.env ->
  Declarations.mutual_inductive_body -> Declarations.mutual_inductive_body ->
  (umap, diff) result
(** Whole-block equality, modulo the universe bijection. Every field that can
    make two blocks different types is compared: the number and order of the
    mutual types, each type's name and each constructor's name in order, the
    parameter context, the numbers of indices and of constructor arguments,
    each arity and sort, each constructor type (both [mind_user_lc] and
    [mind_nf_lc]), the universe kind and its constraints (monomorphic levels
    through the bijection; polymorphic and template contexts positionally,
    including their elimination constraints), finiteness, the record shape and
    its projections, template data, [mind_private], variance, the squash and
    relevance data, the recursive-argument tree, the VM reloc table and the
    typing flags.

    [env] is not consulted: the comparison is syntactic. It is in the
    signature because a conversion-based comparison would need it, and
    callers should not have to change when one appears.

    Not compared, deliberately: [mind_typing_flags.conv_oracle] (transparency
    settings are not part of a type's identity) and section data, which cannot
    appear in a loaded library. *)

(** {6 The load-time step} *)

val merge : Environ.env -> Names.ModPath.t -> Univ.ContextSet.t ->
  Mod_declarations.module_body ->
  Environ.env * Univ.UnivConstraints.t * Mod_declarations.module_body
(** [merge env mp univs mb] is called from [Safe_typing.import] with the
    library's own universe context. It returns the environment with the
    universe equalities the accepted merges need, those equalities, and the
    library's module body with every matched inductive renamed and with
    every earlier merge of this process applied. A no-op when [enabled ()]
    is false.

    The caller must record the returned equalities in the compilation unit's
    own constraints. A term the unit writes out can type-check only under
    them, and undoing the names does not undo that: without the record, a
    reader that never heard of the option accepts the term and may then add
    a contradicting constraint, which is a proof of [False].

    A universe-polymorphic block never merges in v1, whatever [eq_mib] says
    about it; [eq_mib] still compares one, for the comparator's sake, and the
    refusal is here. A template-polymorphic block does merge, on
    [equal_template]'s verdict. *)

val apply_earlier_merges : Names.ModPath.t ->
  Mod_declarations.module_body -> Mod_declarations.module_body
(** The merges already made, applied to a library's body without looking for
    new ones. A checker that type-checks a library in the environment those
    merges produced must give it a body that names them the way that
    environment does; [merge] applies the same substitution again
    afterwards, which is idempotent. *)

(** {6 One environment's merges}

    What [merge] remembers between two loads -- the shape index of the
    blocks loaded so far, each loaded library's universe context, the merges
    made and the substitution that applies them -- describes the one
    environment those libraries were loaded into: a candidate is looked up
    in the environment [merge] is given. A process that builds a second
    environment from nothing, as [rocqchk -compare] does for the challenge,
    loads it with a state of its own and puts the first one back afterwards.
    The option ([enabled], [verbose]) is the process's setting and is not
    part of the state. *)

type state

val fresh_state : unit -> state
(** No library loaded, no merge made. *)

val swap_state : state -> state
(** [swap_state s] installs [s] and returns the state it replaces, as
    [CheckLibrary.swap_tables] does for the checker's library tables. The
    installed state's index is updated in place, so a state value is handed
    back by the next swap, not kept as a snapshot to install twice. *)

(** {6 Two directions the merge refuses, both fail-closed} *)

(** A universe-polymorphic block never merges in v1, whatever [eq_mib] says
    about it; [eq_mib] still compares one, for the comparator's sake, and the
    refusal is here. A template-polymorphic block does merge, on
    [equal_template]'s verdict: an [Inductive w (A : Type)] with no attribute
    is made template automatically, so refusing template blocks would refuse
    every parameterised [Type]-valued type.



    The merge renames the later-loaded copy, and only the loaded structure
    is renamed: the name table still resolves [Agent.tree] to the kerpair
    the agent's library declared, because that globref is built from
    [Safe_typing.mind_of_delta_kn_senv], which this does not touch. So an
    ascription in the direction the grader needs -- [Definition chk :
    Spec.Stmt := Agent.thm], the already-loaded copy's statement with the
    later copy's term -- works, while the opposite one, [Definition x :
    Agent.tree := Spec.Leaf], is refused with a message that prints the same
    name on both sides. Making it work means rewriting that globref too;
    that is not done here, and until it is, a checker file must be written
    in the first direction.

    A module alias whose resolver points at a name this run merged into is
    refused even when the alias itself needed no merge ([Module MS := Spec.]
    in a run that merged something else into [Spec]): which copy an alias
    names cannot be read back out of its resolver, so the refusal is the
    conservative answer rather than a guess. *)

(** A {e private} block never merges either. Only the file that declared one
    may match on it, so a file may axiomatise a distinction away and stay
    consistent; two files that declare the same private type are two
    quotients, not one type, and identifying them lets one file's match see
    through the other's axiom, which is a proof of [False]. [eq_mib] still
    compares them, for the comparator; the refusal is in [merge]. *)

(** {6 Known limits, none of them fixed here}

    - The bytecode VM compares constructed values by tag and arity, the
      kernel compares constructor names, so the two can disagree about a
      term that mixes two copies' constructors -- which only a library
      built with this option contains. With the option on they agree: a
      check may use [-bytecode-compiler yes]. The one disagreement needs
      all three of the option OFF, the mixed-name library admitted
      unchecked ([-norec] or [-admit], so nothing re-derives it), and the
      VM on; there the VM accepts what the kernel refuses. A reader
      without the option must therefore not admit a merge-written library
      unchecked. [merge_inductives_vm_agree] pins every cell of that,
      including the one that disagrees.

    - This module's state ([index], [library_univs], [merged],
      [merge_targets], [global_subst]) lives in plain refs, not in the
      kernel summary, so it is not rolled back. A [Require] inside a
      [Section], a [Succeed Require] or a [Fail Fail Require] with the
      option on ends in an anomaly rather than a clean error. It fails
      closed, and no batch [rocq c] or [rocqchk] run reaches it.

    - A merge nobody asked for is still a merge: its universe equalities go
      into the graph and into the compilation unit's constraints, so two
      libraries that are each valid can become unloadable together. The
      option has no "merge only against library X" mode.

    - Which of two copies keeps its name is still decided by load order --
      the one loaded first is the canonical one -- and the two binaries do
      not use the same order. [rocq c] loads them in [Require]
      order. [rocqchk] builds its list in
      [CheckLibrary.recheck_library]: each argument's dependency closure,
      dependencies before dependents, but the whole list reversed at the
      end, so the arguments are taken last-first and the plainly checked
      ones come before the [-norec] ones. (The [List.rev] in
      [coqchk_main.compile_files] only undoes the prepending its argument
      parser does; it is the reversal in [recheck_library] that decides
      this.) A library's own terms no longer care, because the checker
      applies the merges it has already made to a library's body before it
      checks it ([apply_earlier_merges]) and the loaded body's resolver is
      updated to match, so a checker file that names a statement library's
      inductive directly is accepted in every order. What is still order
      dependent is which name appears in a message, and the direction
      recorded above. Every difference it makes is a refusal, never an
      acceptance.

    - A library that aliases another whose inductive this run merged
      ([Module A := Agent.] after [Agent]'s block was merged) cannot be
      written out: the alias's resolver records the merged canonical name
      and which copy it names is not recoverable from it, so the compile is
      refused rather than guessed at. Compiling that file without the
      option is the way out. *)

(** {6 Undoing a merge on the way out} *)

val unmerging : unit -> bool

val unmerge_exported :
  Mod_declarations.structure_body -> Mod_declarations.structure_body
(** Undo every name {e this process} merged. A cross-file canonical name that
    came from somewhere else -- a module alias, say -- is left alone. *)

val unmerge_constr : Constr.t -> Constr.t
(** The same, for one term: used on the opaque proof table, which is written
    outside the structure. *)

val unmerge_delta : Mod_subst.delta_resolver -> Mod_subst.delta_resolver
(** The same, for the delta resolver a library exports beside its structure.
    A resolver entry that points at a name this run merged into cannot be
    undone -- which copy an alias names is not recoverable from it -- so this
    refuses to write the library rather than guess. *)
