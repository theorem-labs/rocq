(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Jean-Christophe Filliâtre as part of the rebuilding of
   Coq around a purely functional abstract type-checker, Dec 1999 *)

(* This file provides the entry points to the kernel type-checker. It
   defines the abstract type of well-formed environments and
   implements the rules that build well-formed environments.

   An environment is made of constants and inductive types (E), of
   section declarations (Delta), of local bound-by-index declarations
   (Gamma) and of universe constraints (C). Below E[Delta,Gamma] |-_C
   means that the tuple E, Delta, Gamma, C is a well-formed
   environment. Main rules are:

   empty_environment:

     ------
     [,] |-

   push_named_assum(a,T):

     E[Delta,Gamma] |-_G
     ------------------------
     E[Delta,Gamma,a:T] |-_G'

   push_named_def(a,t,T):

     E[Delta,Gamma] |-_G
     ---------------------------
     E[Delta,Gamma,a:=t:T] |-_G'

   add_constant(ConstantEntry(DefinitionEntry(c,t,T))):

     E[Delta,Gamma] |-_G
     ---------------------------
     E,c:=t:T[Delta,Gamma] |-_G'

   add_constant(ConstantEntry(ParameterEntry(c,T))):

     E[Delta,Gamma] |-_G
     ------------------------
     E,c:T[Delta,Gamma] |-_G'
   add_mind(Ind(Ind[Gamma_p](Gamma_I:=Gamma_C))):


     E[Delta,Gamma] |-_G
     ------------------------
     E,Ind[Gamma_p](Gamma_I:=Gamma_C)[Delta,Gamma] |-_G'

   etc.
*)

open Util
open Names
open Declarations
open Mod_declarations
open Constr
open Context.Named.Declaration

module NamedDecl = Context.Named.Declaration

(** {6 Safe environments }

  Fields of [safe_environment] :

  - [env] : the underlying environment (cf Environ)
  - [modpath] : the current module name
  - [modvariant] :
    * NONE before coqtop initialization
    * LIBRARY at toplevel of a compilation or a regular coqtop session
    * STRUCT (params,oldsenv) : inside a local module, with
      module parameters [params] and earlier environment [oldsenv]
    * SIG (params,oldsenv) : same for a local module type
  - [modresolver] : delta_resolver concerning the module content, that needs to
    be marshalled on disk. Its root must be [modpath].
  - [paramresolver] : delta_resolver in scope but not part of the library per
    se, that is from functor parameters and required libraries
  - [revstruct] : current module content, most recent declarations first
  - [modlabels] and [objlabels] : names defined in the current module,
      either for modules/modtypes or for constants/inductives.
      These fields could be deduced from [revstruct], but they allow faster
      name freshness checks.
 - [univ] : current universe constraints
 - [future_cst] : delayed opaque constants yet to be checked
 - [required] : names and digests of Require'd libraries since big-bang.
      This field will only grow
 - [loads] : list of libraries Require'd inside the current module.
      They will be propagated to the upper module level when
      the current module ends.
 - [local_retroknowledge]

*)

type vodigest =
  | Dvo_or_vi of Digest.t        (* The digest of the seg_lib part *)

let digest_match ~actual ~required =
  match actual, required with
  | Dvo_or_vi d1, Dvo_or_vi d2 -> String.equal d1 d2

(** Per-declaration interface digest of one compiled library's exported
    constants/inductives, keyed by the FULL QUALIFIED dotted path (e.g.
    [M.foo] for a constant nested one level deep, [foo] for a top-level
    one -- binary-equivalence-taiga#841 round 8/kd1/kd2: NOT a bare
    [Id.t], which let two differently-located declarations sharing a
    short name collide under one key and mask each other in
    [iface_subset_ok]; see [iface_entries_of_sfb]'s doc comment): for
    every [SFBconst]/[SFBmind] entry anywhere in the library -- at the
    top level or nested inside any number of [Module]s, recursively --
    a digest of everything a dependent could ever observe through it --
    type, universe context, typing flags, and the actual value when
    transparent -- deliberately excluding an opaque proof's own term and
    whether the constant is [Undef] ([Admitted], no body) or [OpaqueDef]
    (whatever handle [Qed] assigned it): a dependent can never unfold
    either one, so neither is part of the exported interface. A
    rewrite-rules block or an unapplied functor's own body gets a single
    opaque, exact-match-only entry instead (same doc comment). A [Module
    Type]'s own fields ARE included (round 9/mt1 reversed the earlier
    exclusion), each basename-marked uncollidable with any real
    identifier (see [modtype_entry_marker]'s doc comment); a [Module]'s
    or [Module Type]'s own NAME is ALSO an entry here, unmarked (round 9
    P1/mns1/mtns1 -- see [iface_entries_of_sfb]'s doc comment). [None] is
    reserved for a library this mechanism cannot
    represent AT ALL (one with non-empty retroknowledge, [Register]/
    [Primitive] -- see [export]'s own doc comment on
    [has_retroknowledge]): such a library falls back to the whole-library
    digest only, i.e. stock behavior. *)
type iface_table = (string * Digest.t) array

(** [recorded] is what a dependent saw of a library at its own compile
    time; [live] is that library's current table. Every entry the
    dependent recorded must still be present with the same digest; extra
    entries in [live] (declarations added since) are ignored -- that is
    exactly what lets an unused addition skip invalidating existing
    dependents. A name the dependent recorded that has since vanished (a
    statement removed or renamed) fails the check. Sound against two
    DIFFERENT declarations sharing a bare basename (round 8/kd1/kd2)
    ONLY because every key here is a full qualified path, unique within
    one library -- [Array.find_opt] finding "the first" match is the
    bug this fixes, not something this function's own logic works around. *)
let iface_subset_ok ~recorded ~live =
  let find key = Array.find_opt (fun (key', _) -> String.equal key key') live in
  Array.for_all (fun (key, d) -> match find key with
      | Some (_, d') -> String.equal d d'
      | None -> false)
    recorded

(** The basename (innermost segment) of a qualified path built by
    [iface_entries_of_sfb] -- used ONLY by [flatten_closure] to populate
    its OWN, deliberately coarser, bare-name [closure_table] (see that
    function's doc comment for why cross-library G7 shadow detection
    needs the bare name, never a qualified one). Defined here (ahead of
    [iface_entries_of_sfb] itself, far below) purely because
    [flatten_closure] needs it first. *)
let basename_of_qualified_path (path : string) : Id.t =
  let base = match String.rindex_opt path '.' with
    | Some i -> String.sub path (i + 1) (String.length path - i - 1)
    | None -> path
  in
  Id.of_string_soft base

(** Whether the basename a qualified path reduces to is one of this
    file's reserved, digit-leading markers ([opaque_entry_prefix] or
    [modtype_entry_marker], defined below) -- used ONLY by
    [flatten_closure] to EXCLUDE such entries from cross-library G7
    shadow detection entirely (round 9 P3/mkc1: the marker only
    guarantees uniqueness from any REAL identifier, never uniqueness
    ACROSS different libraries that independently reuse the SAME marker
    on their own, unrelated, coincidentally-same-named field -- two
    unrelated module types in different libraries both naming a field
    "x" produce the identical marked basename "0usage_cutoff_modtype_x",
    which [flatten_closure]'s cross-library comparison would otherwise
    treat as one library shadowing the other's "x", even though neither
    library's dependent ever resolves a bare "x" to either module
    type's abstract field). [iface_subset_ok] (the SAME-library check,
    keyed by the FULL qualified path, never just the basename) is
    unaffected: a marked field's own content changing within ITS
    OWNING library is still refused exactly as before. *)
let is_marked_basename (id : Id.t) : bool =
  let s = Id.to_string id in
  String.length s > 0 && (match s.[0] with '0' .. '9' -> true | _ -> false)

(** Reserved, mutually-disjoint G7 namespace tags for a [Module]'s vs. a
    [Module Type]'s own LABEL (round 12). Defined here, ahead of
    [closure_subset_ok], because round 13 needs both names there -- see
    [iface_entries_of_sfb]'s own doc comment (far below, where they are
    applied via [mark_basename]) for the full history and the
    [Definition a#b := 0.] syntax-error argument for why ['#'] makes
    either tag uncollidable with any real identifier. *)
let module_label_marker = "zmodlabel#"
let modtype_label_marker = "zmodtypelabel#"

(** Strips [prefix] from the front of [s], if present. *)
let strip_prefix (prefix : string) (s : string) : string option =
  let lp = String.length prefix in
  if String.length s >= lp && String.equal (String.sub s 0 lp) prefix
  then Some (String.sub s lp (String.length s - lp))
  else None

(** A dependency record as it is written to and read from disk: the
    library's name, its whole-library digest, its per-declaration interface
    table (if representable), the digest of its exported vernac-object
    state (Hints/Instances/Notations/Ltac2/Canonical Structures -- computed
    by the vernac layer, which is the only layer that can see
    [Declaremods.library_objects]; the kernel only ever stores and compares
    the opaque [Digest.t] it is handed), and the digest of its OWN
    [(comp_univs, comp_sorts)] pair (binary-equivalence-taiga#841 Review841
    G2: with neither digest covering the library's global universe
    constraints, a dependency that drops/adds a monomorphic constraint
    without touching any declaration's own per-constant digest or any
    exported vernac object -- e.g. a bare [Universe]/[Constraint] command --
    passed the relaxed fallback below undetected, even though a FRESH
    compile of the dependent could fail or produce a different proof
    obligation against the changed constraint set). Every library has SOME
    object state (possibly empty) and SOME univs/sorts pair (possibly
    empty), so neither is ever optional -- unlike [iface_table option],
    which is genuinely absent for a library whose top level isn't a flat
    constant/inductive run. *)
(** binary-equivalence-taiga#841 Review841 G1/round-3: [vernac_iface] is a
    KEYED per-declaration vernac-object digest table (same shape as
    [iface_table] above, checked the same way by [iface_subset_ok]) for
    declarations whose non-presentational interface has no independent
    kernel-level coverage via [iface_table] itself -- today, a CONSTANT's
    [cst_locl]/[cst_warn] plus its EFFECTIVE, resolved implicits/argument-
    scopes (see [Declaremods.G1Partition.vernac_iface_entries], which
    computes this at [end_library] time from the library's own completed
    environment, not from raw leaf libobjects). Round 3 found the
    PREDECESSOR of this field (an unkeyed [Digest.t array], SET-membership
    checked) unsound twice over: Review841's "l1"/"d1" (a `Local
    Definition`/`#[deprecated]` change on one declaration could regress a
    flat, unrelated digest elsewhere in the same SET) and "i1"/"i3" (an
    added/reordered `Arguments` override for an EXISTING name was wrongly
    tolerated as an ignorable "addition," since nothing about the entry
    SET changes when the EFFECTIVE value for that name does). Keying by
    name and checking per-key, exactly like [iface_table], closes both:
    an edit to declaration X's own entry can only ever affect X's own
    check, and an override/reorder changes X's digest in place rather
    than hiding behind set membership. *)
let iface_subset_ok_vernac = iface_subset_ok

(** A library's own [iface_table] entry, tagged with the OWNING
    library's [DirPath.t] -- see [flatten_closure]'s doc comment for why
    this is NOT a flat [(Id.t * Digest.t) array] like [iface_table]
    (round 5's first attempt at this used that shape and a bug was found
    before it shipped: a "last writer wins" flatten across DIFFERENT
    libraries that happen to share a short name silently discards
    whichever library's digest doesn't "win" the merge, which can hide a
    genuine collision -- g7_shadowing_refused's own X/A pair, where X's
    STATIC, unchanged `f` entry always wins the merge over A's, as long
    as X's dirpath sorts after A's -- making A's change to `f`
    invisible). *)
type closure_table = (DirPath.t * Id.t * Digest.t) array

type library_info =
  DirPath.t * vodigest * iface_table option * Digest.t * Digest.t * iface_table
  * closure_table * Digest.t
(** The last two components ([closure_names]/[closure_none_digest], added
    binary-equivalence-taiga#841 Review841 round 5) close g7exp/g7pre/
    g7mod/g7ctor -- see [flatten_closure]'s doc comment below. *)

(** binary-equivalence-taiga#841 Review841 G7, round 5 (closing g7exp/
    g7pre/g7mod/g7ctor -- issuecomment-6189455137/round-4 review
    issuecomment-6189398514). The PREDECESSOR mechanism
    ([used_names_of_needed]/[added_label_collision], removed this round)
    only unioned the [iface_table] keys of a library's DIRECT, root-only
    [needed] array, missing every name that becomes visible only through
    a dependency's OWN transitive closure: a name re-exported via
    [Require Export] several hops down (g7exp), a prelude/stdlib name
    whose OWNING library isn't itself a direct dependency (g7pre -- the
    auto-required prelude only re-exports it), any dependency whose
    [iface_table] is [None] (a nested module, g7mod), and a constructor
    label (not separately keyed by the OLD [iface_table_of_struct],
    g7ctor -- see that function's own fix alongside this one).

    Fix: rather than approximate "what could this library have used"
    from its own direct deps, record, for EVERY library visible in the
    FULL transitive closure at compile time (-- [senv.required]'s
    complete binding set, every library this coqc process has loaded so
    far when THIS library is compiled, unfiltered by [req_root]; see
    [export] below), EVERY one of ITS OWN [(Id.t, Digest.t)] entries,
    tagged with that library's own [DirPath.t] (a [closure_table], NOT
    merged/flattened across libraries -- see that type's doc comment for
    why). This does NOT require D1's [comp_transitive_deps]: a library's
    own closure is fully populated in [senv.required]/[current_libs] by
    the time it is compiled or checked, since every file in a require
    graph is loaded bottom-up before its dependents are even considered
    (confirmed by inspection of [vernac/library.ml]'s require pipeline:
    [register_library]/[Safe_typing.import] for a file runs only after
    [intern_library_deps] has fully recursed over that file's WHOLE
    transitive closure). This field only tracks NAME EXISTENCE for
    shadow detection -- it never re-validates a transitively-required
    library's full CONTENT the way D1's induction argument would, so it
    closes a narrower problem than D1's Blocker.

    At CHECK time the SAME per-library tagging is recomputed from the
    live [current_libs] map (which, by construction, holds the SAME full
    closure, live) and compared via [closure_subset_ok]: for every
    recorded [(dp, id, digest)] triple, the SAME triple must still be
    present in the live set (a library's own declaration changing or
    disappearing fails this, same as [iface_subset_ok]); AND, for every
    [id] the recorded set names (from whichever [dp] originally defined
    it), the live set must not have GAINED a triple for that SAME [id]
    from a DIFFERENT [dp] -- that is exactly "someone new now defines a
    name this dependent's closure already had a binding for," the shadow
    hazard G7 exists to refuse. An id's recorded [dp] set staying fixed
    while only EXTRA, entirely NEW ids appear (from any library) is the
    ordinary, G1-intended "unused addition," explicitly allowed.

    A library whose OWN [iface_table] is [None] (non-empty
    retroknowledge only -- see [iface_table]'s doc comment;
    [iface_entries_of_sfb] now recurses into nested modules/module
    types and folds a rewrite-rules block or unapplied functor into an
    opaque PER-CHUNK entry of the SAME per-id table instead of forcing
    this) cannot be enumerated into the per-id table at all, so a
    SEPARATE digest ([closure_none_digest]) covers the sorted
    [(DirPath.t, vodigest)] pairs of every such entry in the closure: if
    such a library's content changes (its own digest differs) or one is
    added/removed, this digest changes and the check fails -- scoped to
    libraries that actually changed, so an untouched, unrelated
    retroknowledge-bearing library anywhere in a large closure (e.g.
    Corelib) does not poison every reuse decision.

    Round 9 P3/mkc1: a marked basename ([is_marked_basename], covering
    both [opaque_entry_prefix] and [modtype_entry_marker]) is excluded
    from [triples] below entirely, never merely relied on to not match --
    the marker only guarantees uniqueness from a REAL identifier's
    basename, not uniqueness ACROSS two unrelated libraries that
    independently produce the SAME marked basename (e.g. two module
    types in different libraries both naming a field "x"), which a
    naive inclusion would wrongly treat as one shadowing the other. *)
let flatten_closure (entries : (DirPath.t * vodigest * iface_table option) list) : closure_table * Digest.t =
  let triples =
    List.concat_map (fun (dp, _, iface) -> match iface with
        | Some tbl ->
          Array.to_list tbl
          |> List.filter_map (fun (path, d) ->
              let id = basename_of_qualified_path path in
              if is_marked_basename id then None else Some (dp, id, d))
        | None -> [])
      entries
  in
  let triples = Array.of_list triples in
  Array.sort (fun (dp1, id1, _) (dp2, id2, _) ->
      let c = DirPath.compare dp1 dp2 in
      if c <> 0 then c else Id.compare id1 id2)
    triples;
  let none_entries =
    List.filter_map (fun (dp, Dvo_or_vi d, iface) ->
        match iface with None -> Some (DirPath.to_string dp, d) | Some _ -> None)
      entries
  in
  let none_entries = List.sort (fun (a, _) (b, _) -> String.compare a b) none_entries in
  let none_digest = Csha256.digest (Marshal.to_string none_entries []) in
  (triples, none_digest)

(** Groups a [closure_table] by [Id.t], each id mapped to the (possibly
    several, if unrelated libraries happen to share a short name)
    [(DirPath.t * Digest.t)] pairs that define it -- the shape
    [closure_subset_ok] below needs to detect both a changed/removed
    declaration (within one [dp]) and a NEW [dp] appearing for an
    already-recorded [id] (the shadow case). *)
let group_closure (t : closure_table) : (DirPath.t * Digest.t) list Id.Map.t =
  Array.fold_left (fun acc (dp, id, d) ->
      let l = try Id.Map.find id acc with Not_found -> [] in
      Id.Map.add id ((dp, d) :: l) acc)
    Id.Map.empty t

(** binary-equivalence-taiga#841 round 13 (ik1-ik4/ik6, Main/reviewer):
    [Modintern.lookup_module_or_modtype] tries a MODULE lookup first and
    falls back to a MODULE TYPE only for [ModAny]-kind queries --
    confirmed by reading every [ModAny]/[ModType] interning site in
    [interp/modintern.ml] and [vernac/declaremods.ml]:
    [declare_one_include_core] (`Include`) interns with [ModAny]
    (declaremods.ml:1484); so does a functor APPLICATION's argument
    (modintern.ml:123, guarded immediately after by
    [error_application_to_module_type] if the result is a module type --
    an error, not a silent accept, so it cannot itself cause a stale
    reuse). Every seal/signature site ([: T], [Declare Module : T], a
    functor's OWN parameter signature, [Module Type] abbreviation) interns
    with the literal [ModType] kind, which [lookup_module_or_modtype]
    (modintern.ml:54) skips the module lookup for ENTIRELY (`if kind ==
    ModType then raise Not_found`) -- no fallback the OTHER way exists
    anywhere in this tree. So `Include T`, resolving [T] via [ModAny], can
    silently re-resolve to a NEW, unrelated MODULE of the same bare name
    if one appears later (reachable only transitively, e.g. through a
    [Require Export]) -- B's own closure never recorded [T] under the
    MODULE tag at all (only under the MODULE TYPE tag, since that is what
    [T] resolved to at B's own compile time), so the ordinary per-id
    check below, which only ever visits a key already present in
    [recorded], never looks at the new module-tagged key [live] gains.

    Fix, ONE-DIRECTIONAL: before the ordinary check, fold every RECORDED
    entry keyed under [modtype_label_marker ^ base] into the group keyed
    under [module_label_marker ^ base] too (creating that key if B never
    recorded a module there at all) -- so a NEW live module-tagged dp for
    that bare name is only accepted if it is ALSO one of the dps already
    recorded as having defined EITHER the module type or (if any) the
    module itself. The REVERSE never happens: a module-type-tagged live
    entry is checked ONLY against recorded module-type entries, since no
    lookup falls back from [ModType] to a module. The shared
    [module_label_digest] constant (same value for every label regardless
    of kind, by design -- see that constant's own doc comment) makes the
    borrowed digest-equality half of the check trivially satisfied, so
    folding introduces no spurious content-mismatch false positive. *)
let closure_subset_ok ~recorded ~live =
  let rec_grouped = group_closure recorded in
  let live_grouped = group_closure live in
  (* allowed_by_modtype: a dp is additionally allowed for a live MODULE-kind
     id if recorded has a MODULE-TYPE entry for the same bare name from
     that exact dp -- never the reverse, and never a requirement that a
     module-type-only name must also have a live module counterpart (that
     would wrongly refuse every module type with no same-named module
     anywhere, e.g. mkc1/mkc2/mt1). *)
  let allowed_by_modtype id dp =
    match strip_prefix module_label_marker (Id.to_string id) with
    | None -> false
    | Some base ->
      (match Id.Map.find_opt (Id.of_string_soft (modtype_label_marker ^ base)) rec_grouped with
       | None -> false
       | Some rec_modtype_dps -> List.exists (fun (dp', _) -> DirPath.equal dp dp') rec_modtype_dps)
  in
  Id.Map.for_all (fun id rec_dps ->
      match Id.Map.find_opt id live_grouped with
      | None -> false
      | Some live_dps ->
        List.for_all (fun (dp, d) ->
            List.exists (fun (dp', d') -> DirPath.equal dp dp' && String.equal d d') live_dps)
          rec_dps
        && List.for_all (fun (dp, _) ->
            List.exists (fun (dp', _) -> DirPath.equal dp dp') rec_dps
            || allowed_by_modtype id dp)
          live_dps)
    rec_grouped
  &&
  (* A live MODULE-kind id never recorded at all (B used it only through
     Include/ModAny, so it was recorded under the MODULE-TYPE tag, never
     the MODULE one) still needs checking -- ik1-ik4/ik6's actual shape. *)
  Id.Map.for_all (fun id live_dps ->
      Id.Map.mem id rec_grouped
      || match strip_prefix module_label_marker (Id.to_string id) with
         | None -> true
         | Some base ->
           (match Id.Map.find_opt (Id.of_string_soft (modtype_label_marker ^ base)) rec_grouped with
            | None -> true (* nothing recorded under this name as a module type either; an ordinary new addition *)
            | Some rec_modtype_dps ->
              List.for_all (fun (dp, _) ->
                  List.exists (fun (dp', _) -> DirPath.equal dp dp') rec_modtype_dps)
                live_dps))
    live_grouped


(** The relaxed acceptance predicate, shared by every loader that is
    allowed to use it (the kernel's own [check_required] below, and
    vernac/library.ml's and topbin/rocqnative.ml's own
    [intern_mandatory_library]): accept iff the whole-library digest
    matches (stock, unconditionally sound), OR ALL OF (a) every declaration
    the dependent recorded still has an identical digest in the live
    table, (b) the live library's exact-equality objects digest is EXACTLY
    what the dependent recorded (Hints/Instances/Notations/Ltac2/Canonical
    Structures/Coercions/univ-constraint-source objects, plus whatever
    IMPLICITS/ARGUMENTS-SCOPE objects aren't locally keyed -- any change
    anywhere in that remainder forces a rebuild, deliberately
    conservative), (c) the live library's [(comp_univs, comp_sorts)]
    digest is EXACTLY what the dependent recorded (G2), (d) every KEYED
    [vernac_iface] entry (CONSTANT's `cst_locl`/`cst_warn`, INDUCTIVE/
    constructor entries, plus every target's EFFECTIVE implicits/
    argument-scopes, G1/round-3 + round-5) the dependent recorded is
    still present with an EQUAL digest in the live table (subset by name,
    extras ignored, same shape as (a)), AND (e) the live FULL CLOSURE's
    flat name table is still a superset-with-identical-digests of what
    the dependent recorded, AND (f) the live closure's None-iface-entry
    digest is unchanged (G7, round 5). [coqchk] must NEVER call this: see
    [check_required_strict] below, which is the original digest-only
    check with nothing else reachable from it. *)
let dep_ok ~actual ~required ~actual_iface ~required_iface
    ~actual_objects_digest ~required_objects_digest
    ~actual_univs_digest ~required_univs_digest
    ~actual_vernac_iface ~required_vernac_iface
    ~actual_closure_names ~required_closure_names
    ~actual_closure_none_digest ~required_closure_none_digest =
  digest_match ~actual ~required ||
  ((match required_iface, actual_iface with
    | Some recorded, Some live -> iface_subset_ok ~recorded ~live
    | _ -> false) &&
   Digest.equal required_objects_digest actual_objects_digest &&
   Digest.equal required_univs_digest actual_univs_digest &&
   iface_subset_ok_vernac ~recorded:required_vernac_iface ~live:actual_vernac_iface &&
   closure_subset_ok ~recorded:required_closure_names ~live:actual_closure_names &&
   Digest.equal required_closure_none_digest actual_closure_none_digest)

(** Functor and funsig parameters, most recent first *)
type module_parameters = (MBId.t * module_type_body) list

type permanent_flags = {
  rewrite_rules_allowed : bool;
}

module ParamResolver :
sig
  type t
  val empty : DirPath.t -> t
  val add_delta_resolver : ModPath.t -> Mod_subst.delta_resolver -> t -> t
  val constant_of_delta_kn : t -> KerName.t -> Constant.t
  val mind_of_delta_kn : t -> KerName.t -> MutInd.t
end =
struct
  type t = {
    root : DirPath.t;
    data : Mod_subst.delta_resolver ModPath.Map.t;
    (** Invariant: No [MPdot] in data *)
  }

  let empty root = {
    root = root;
    data = ModPath.Map.empty;
  }

  let rec head mp = match mp with
  | MPfile _ | MPbound _ -> mp
  | MPdot (mp, _) -> head mp

  let add_delta_resolver mp delta preso =
    let self = MPfile preso.root in
    let data =
      if ModPath.subpath self mp then
        match ModPath.Map.find_opt self preso.data with
        | None ->
          (* we were at toplevel *)
          ModPath.Map.add self delta preso.data
        | Some reso ->
          ModPath.Map.add self (Mod_subst.add_delta_resolver delta reso) preso.data
      else
        let () = match mp with
        | MPfile _ | MPbound _ -> ()
        | MPdot _ -> assert false
        in
        let () = assert (not (ModPath.Map.mem mp preso.data)) in
        ModPath.Map.add mp delta preso.data
    in
    { preso with data }

  let kn_of_delta preso kn =
    let head = head (KerName.modpath kn) in
    match ModPath.Map.find_opt head preso.data with
    | None -> kn
    | Some delta -> Mod_subst.kn_of_delta delta kn

  let constant_of_delta_kn preso kn = Constant.make kn (kn_of_delta preso kn)

  let mind_of_delta_kn preso kn = MutInd.make kn (kn_of_delta preso kn)

end

type compiled_library = {
  comp_name : DirPath.t;
  comp_mod : module_body;
  comp_univs : Univ.ContextSet.t;
  comp_sorts : Sorts.QContextSet.t;
  comp_deps : library_info array;
  comp_flags : permanent_flags;
  (** [None] when the library's top level isn't a flat constant/inductive
      run (see [iface_table]'s doc comment). *)
  comp_iface : iface_table option;
  (** Digest of this library's exported [Declaremods.library_objects]
      (Hints/Instances/Notations/Ltac2/Canonical Structures), computed by
      the vernac layer from the AS-EXPORTED value (post any
      [Require (safe)]-style filtering, never re-derived from source) and
      handed in through [export]'s [~objects_digest] parameter -- the
      kernel treats it as an opaque [Digest.t] it stores and compares,
      never interprets. *)
  comp_objects_digest : Digest.t;
  (** Digest of this library's OWN [(comp_univs, comp_sorts)] pair, computed
      by the kernel itself at [export] time (unlike
      [comp_objects_digest], nothing outside the kernel needs to hand this
      in -- [comp_univs]/[comp_sorts] above are already right here).
      binary-equivalence-taiga#841 Review841 G2: see [library_info]'s doc
      comment for the blind spot this closes. *)
  comp_univs_digest : Digest.t;
  (** G1/round-3: KEYED per-declaration vernac-interface digests (see
      [iface_subset_ok_vernac]'s doc comment). Handed in through
      [export]'s [~vernac_iface] parameter, same provenance as
      [comp_objects_digest]. *)
  comp_vernac_iface : iface_table;
  (** G7 round 5: this library's full transitive closure, flattened. See
      [flatten_closure]'s doc comment. *)
  comp_closure_names : closure_table;
  comp_closure_none_digest : Digest.t;
}

type reimport = compiled_library * Vmlibrary.on_disk * vodigest

type required_lib = {
  req_root : bool; (* true if a root of the dependency DAG *)
  req_digest : vodigest;
  req_iface : iface_table option;
  req_objects_digest : Digest.t;
  req_univs_digest : Digest.t;
  req_vernac_iface : iface_table;
}

(** Part of the safe_env at a section opening time to be backtracked *)
type section_data = {
  rev_env : Environ.env;
  rev_univ : Univ.ContextSet.t;
  rev_qualities : Sorts.QVar.Set.t * Sorts.ElimConstraints.t;
  rev_objlabels : Id.Set.t;
  rev_reimport : reimport list;
  rev_revstruct : structure_body;
  rev_paramresolver : ParamResolver.t;
}

module HandleMap = Opaqueproof.HandleMap

(** We rely on uniqueness of pointers to provide a simple implementation of
    kernel certificates. For this to work across processes, one needs the
    safe environments to be marshaled at the same time as their corresponding
    certificates and sharing to be preserved. *)
module Nonce :
sig
  type t
  val create : unit -> t
  val equal : t -> t -> bool
end =
struct
  type t = unit ref
  let create () = ref ()
  let equal x y = x == y
end

type safe_environment =
  { env : Environ.env;
    sections : section_data Section.t option;
    modpath : ModPath.t;
    modvariant : modvariant;
    modresolver : Mod_subst.delta_resolver;
    paramresolver : ParamResolver.t;
    revstruct : structure_body;
    modlabels : Id.Set.t;
    objlabels : Id.Set.t;
    univ : Univ.ContextSet.t;
    (* maybe should be a qglobal set? *)
    qualities : Sorts.QVar.Set.t * Sorts.ElimConstraints.t;
    future_cst : (Constant_typing.typing_context * safe_environment * Nonce.t) HandleMap.t;
    required : required_lib DirPath.Map.t;
    loads : (ModPath.t * module_body) list;
    local_retroknowledge : Retroknowledge.action list;
    opaquetab : Opaqueproof.opaquetab;
}

and modvariant =
  | NONE
  | LIBRARY
  | SIG of module_parameters * safe_environment (** saved env *)
  | STRUCT of module_parameters * safe_environment (** saved env *)

let rec library_dp_of_senv senv =
  match senv.modvariant with
  | NONE | LIBRARY -> ModPath.dp senv.modpath
  | SIG(_,senv) -> library_dp_of_senv senv
  | STRUCT(_,senv) -> library_dp_of_senv senv

let empty_environment =
  { env = Environ.empty_env;
    modpath = ModPath.dummy;
    modvariant = NONE;
    modresolver = Mod_subst.empty_delta_resolver ModPath.dummy;
    paramresolver = ParamResolver.empty DirPath.dummy;
    revstruct = [];
    modlabels = Id.Set.empty;
    objlabels = Id.Set.empty;
    sections = None;
    future_cst = HandleMap.empty;
    univ = Univ.ContextSet.empty;
    qualities = Sorts.QVar.Set.empty, Sorts.ElimConstraints.empty;
    required = DirPath.Map.empty;
    loads = [];
    local_retroknowledge = [];
    opaquetab = Opaqueproof.empty_opaquetab;
}

let is_initial senv =
  match senv.revstruct, senv.modvariant with
  | [], NONE -> ModPath.equal senv.modpath ModPath.dummy
  | _ -> false

let sections_are_opened senv = not (Option.is_empty senv.sections)

let delta_of_senv senv = senv.modresolver

let constant_of_delta_kn_senv senv kn =
  let mp = KerName.modpath kn in
  if ModPath.subpath senv.modpath mp then Mod_subst.constant_of_delta_kn senv.modresolver kn
  else ParamResolver.constant_of_delta_kn senv.paramresolver kn

let mind_of_delta_kn_senv senv kn =
  let mp = KerName.modpath kn in
  if ModPath.subpath senv.modpath mp then Mod_subst.mind_of_delta_kn senv.modresolver kn
  else ParamResolver.mind_of_delta_kn senv.paramresolver kn

(** The safe_environment state monad *)

type safe_transformer0 = safe_environment -> safe_environment
type 'a safe_transformer = safe_environment -> 'a * safe_environment


(** {6 Typing flags } *)

let set_typing_flags c senv =
  let env = Environ.set_typing_flags c senv.env in
  if env == senv.env then senv
  else { senv with env }

let set_typing_flags flags senv =
  (* NB: we allow changing the conv_oracle inside sections because it
     doesn't matter for consistency. *)
  if Option.has_some senv.sections
  && not (Environ.same_flags flags
            {(Environ.typing_flags senv.env) with
             conv_oracle = flags.conv_oracle;
             share_reduction = flags.share_reduction;
            })
  then CErrors.user_err Pp.(str "Changing typing flags inside sections is not allowed.");
  set_typing_flags flags senv

let set_impredicative_set b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with impredicative_set = b } senv

let set_check_guarded b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with check_guarded = b } senv

let set_check_positive b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with check_positive = b } senv

let set_check_universes b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with check_universes = b } senv

let set_indices_matter indices_matter senv =
  set_typing_flags { (Environ.typing_flags senv.env) with indices_matter } senv

let set_share_reduction b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with share_reduction = b } senv

let set_VM b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with enable_VM = b } senv

let set_native_compiler b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with enable_native_compiler = b } senv

let set_allow_sprop b senv = { senv with env = Environ.set_allow_sprop b senv.env }

let set_rewrite_rules_allowed b senv =
  if b then { senv with env = Environ.allow_rewrite_rules senv.env }
  else senv

(* Temporary sets custom typing flags *)
let with_typing_flags ?typing_flags senv ~f =
  match typing_flags with
  | None -> f senv
  | Some typing_flags ->
    let orig_typing_flags = Environ.typing_flags senv.env in
    let res, senv = f (set_typing_flags typing_flags senv) in
    res, set_typing_flags orig_typing_flags senv

(** {6 Stm machinery } *)

module Certificate :
sig
  type t

  val make : safe_environment -> t

  val universes : t -> Univ.ContextSet.t

  (** Checks whether [dst] is a valid extension of [src] by 1 declaration,
      possibly adding universes and constraints. *)
  val safe_extend : src:t -> dst:t -> t option

  (** [compatible src dst] checks whether [dst] adds exactly 1 declaration
      to an ancestor of [src].
      If it does, the declaration is also valid in [src] (up to universes). *)
  val compatible : safe_environment -> t -> bool
end =
struct

type t = {
  certif_struc : Mod_declarations.structure_body;
  certif_univs : Univ.ContextSet.t;
}

let make senv = {
  certif_struc = senv.revstruct;
  certif_univs = senv.univ;
}

let is_suffix l suf = match l with
| [] -> false
| _ :: l -> l == suf

let safe_extend ~src ~dst =
  if is_suffix dst.certif_struc src.certif_struc then
    Some { certif_struc = dst.certif_struc;
           certif_univs = Univ.ContextSet.union src.certif_univs dst.certif_univs }
  else None

let compatible src dst =
  let dst = dst.certif_struc in
  let src = src.revstruct in
  match dst with
  | [] -> false
  | _ :: dst_base ->
    let rec aux src =
      src == dst_base || match src with
      | [] -> false
      | _ :: src -> aux src
    in
    aux src

let universes c = c.certif_univs

end

type side_effect = {
  seff_certif : Certificate.t CEphemeron.key;
  seff_constant : Constant.t;
  seff_body : HConstr.t option * (Constr.t, Vmemitcodes.body_code option) Declarations.pconstant_body;
  seff_univs : Univ.ContextSet.t;
}
(* Invariant: For any senv, if [Certificate.safe_extend senv seff_certif] returns [Some certif'] then
   [senv + Certificate.universes certif' + (c.seff_constant -> seff_body)] is well-formed
   (if no univ inconsistency). *)

module SideEffects :
sig
  type t
  val repr : t -> side_effect list
  val empty : t
  val is_empty : t -> bool
  val add : side_effect -> t -> t
  val concat : t -> t -> t
  val length : t -> int
  val pop : t -> int -> t * t
end =
struct

module SeffOrd = struct
type t = side_effect
let compare e1 e2 =
  Constant.UserOrd.compare e1.seff_constant e2.seff_constant
end

module SeffSet = Set.Make(SeffOrd)

type t = { seff : side_effect list; elts : SeffSet.t; len : int }
(** Invariant: [seff] is a permutation of the elements of [elts] *)

let repr eff = eff.seff
let empty = { seff = []; elts = SeffSet.empty; len = 0 }
let is_empty { seff; elts; _ } = List.is_empty seff && SeffSet.is_empty elts
let add x es =
  if SeffSet.mem x es.elts then es
  else { seff = x :: es.seff; elts = SeffSet.add x es.elts; len = es.len + 1 }
let concat xes yes =
  List.fold_right add xes.seff yes

let length eff = eff.len

let pop eff n =
  let () = assert (n <= eff.len) in
  let top, rem = List.chop n eff.seff in
  let fold accu x = SeffSet.remove x accu in
  let elts = List.fold_left fold eff.elts top in
  { seff = top; len = n; elts = SeffSet.of_list top }, { seff = rem; len = eff.len - n; elts }

end

type private_constants = SideEffects.t

let debug_print_private_constants seff =
  let open Pp in
  prlist_with_sep spc (fun seff -> Constant.print seff.seff_constant) (SideEffects.repr seff)

let side_effects_of_private_constants l =
  List.rev (SideEffects.repr l)

let length_private = SideEffects.length
let pop_private = SideEffects.pop

(* Only used to push in an Environ.env. *)
let lift_constant c =
  let body = match c.const_body with
  | OpaqueDef _ -> Undef None
  | Def _ | Undef _ | Primitive _ | Symbol _ as body -> body
  in
  { c with const_body = body }

let push_bytecode vmtab code =
  let open Vmemitcodes in
  let vmtab, code = match code with
  | None -> vmtab, None
  | Some (BCdefined (mask, code, patches)) ->
    let vmtab, index = Vmlibrary.add code vmtab in
    vmtab, Some (BCdefined (mask, index, patches))
  | Some BCconstant -> vmtab, Some BCconstant
  | Some (BCalias kn) -> vmtab, Some (BCalias kn)
  in
  vmtab, code

let push_private_constants env eff =
  let eff = side_effects_of_private_constants eff in
  let add_if_undefined env eff =
    if Environ.mem_constant eff.seff_constant env then env
    else
      let (_hbody, cb) = eff.seff_body in
      let vmtab, code = push_bytecode (Environ.vm_library env) cb.const_body_code in
      let cb = { cb with const_body_code = code } in
      let env = Environ.set_vm_library vmtab env in
      Environ.add_constant eff.seff_constant (lift_constant cb) env
  in
  List.fold_left add_if_undefined env eff

let empty_private_constants = SideEffects.empty
let is_empty_private_constants c = SideEffects.is_empty c
let concat_private = SideEffects.concat

let universes_of_private eff =
  let fold acc eff = Univ.ContextSet.union eff.seff_univs acc in
  List.fold_left fold Univ.ContextSet.empty (side_effects_of_private_constants eff)

let constants_of_private eff =
  let fold acc eff = eff.seff_constant :: acc in
  List.fold_left fold [] (side_effects_of_private_constants eff)

let env_of_safe_env senv = senv.env
let env_of_senv = env_of_safe_env

let structure_body_of_safe_env env = env.revstruct

let sections_of_safe_env senv = senv.sections

let rec is_modtype senv =
  match senv.modvariant with
  | STRUCT (_,senv) -> is_modtype senv
  | SIG _ -> true
  | NONE | LIBRARY -> false

let get_section = function
  | None -> CErrors.user_err Pp.(str "No open section.")
  | Some s -> s

let push_context_set ~strict cst senv =
  if Univ.ContextSet.is_empty cst then senv
  else
    let sections = Option.map (Section.push_level_constraints cst) senv.sections
    in
    { senv with
      env = Environ.push_context_set ~strict cst senv.env;
      univ = Univ.ContextSet.union cst senv.univ;
      sections }

let push_qualities ~rigid qs senv =
  if Sorts.QVar.Set.is_empty (fst qs) && Sorts.ElimConstraints.is_empty (snd qs) then
    senv
  else if is_modtype senv then
    CErrors.user_err (Pp.str "Cannot declare global sort qualities inside module types.")
  else if Option.has_some senv.sections then
    CErrors.user_err (Pp.str "Cannot declare global sort qualities inside sections")
  else
    let check_local qv = match Sorts.QVar.repr qv with
    | Sorts.QVar.Global gv ->
      let (dp, _) = Sorts.QGlobal.repr gv in
      let () = assert (DirPath.equal dp (ModPath.dp senv.modpath)) in
      assert (not @@ QGraph.is_declared (Sorts.Quality.QVar qv) (Environ.qualities senv.env))
    | Sorts.QVar.Unif _ | Sorts.QVar.Var _ -> assert false
    in
    let () = Sorts.QVar.Set.iter check_local (fst qs) in
    { senv with
      env = Environ.push_qualities ~rigid qs senv.env ;
      qualities = Sorts.QContextSet.union qs senv.qualities ;
    }

let is_curmod_library senv =
  match senv.modvariant with LIBRARY -> true | _ -> false

let is_joined_environment e = HandleMap.is_empty e.future_cst

(** {6 Various checks } *)

let exists_modlabel l senv = Id.Set.mem l senv.modlabels
let exists_objlabel l senv = Id.Set.mem l senv.objlabels

let check_modlabel l senv =
  if exists_modlabel l senv then Modops.error_existing_label l

let check_objlabel l senv =
  if exists_objlabel l senv then Modops.error_existing_label l

let check_objlabels ls senv =
  Id.Set.iter (fun l -> check_objlabel l senv) ls

(** Are we closing the right module / modtype ?
    No user error here, since the opening/ending coherence
    is now verified in [vernac_end_segment] *)

let check_current_label lab = function
  | MPdot (_,l) -> assert (Id.equal lab l)
  | _ -> assert false

let check_struct = function
  | STRUCT (params,oldsenv) -> params, oldsenv
  | NONE | LIBRARY | SIG _ -> assert false

let check_sig = function
  | SIG (params,oldsenv) -> params, oldsenv
  | NONE | LIBRARY | STRUCT _ -> assert false

let check_current_library dir senv = match senv.modvariant with
  | LIBRARY -> assert (ModPath.equal senv.modpath (MPfile dir))
  | NONE | STRUCT _ | SIG _ -> assert false (* cf Lib.end_compilation *)

(** When operating on modules, we're normally outside sections *)

let check_empty_context senv =
  assert (Environ.empty_context senv.env && Option.is_empty senv.sections)

(** When adding a parameter to the current module/modtype,
    it must have been freshly started *)

let check_empty_struct senv =
  assert (List.is_empty senv.revstruct
          && List.is_empty senv.loads)

(** When loading a library, its dependencies should be already there,
    with the correct digests. *)

let check_required current_libs needed =
  (* binary-equivalence-taiga#841 round 7 (or1/or2): [actual_closure_none_digest]
     stays GLOBAL (every None-iface entry anywhere in the consuming
     process's [current_libs]) exactly as before -- restricting it to
     just the dps a Some-iface closure_table recorded would silently
     make it "empty" whenever NO None-iface library is in that recorded
     set, wrongly MISmatching a recorded NON-empty digest (i.e. any
     library whose closure includes a retroknowledge-bearing library,
     which in practice is every ordinary compile, since Corelib's own
     retroknowledge declarations are always transitively loaded) -- see
     [flatten_closure]'s doc comment on retroknowledge for why this
     digest exists at all. Deliberately NOT scoped the way
     [actual_closure_names] now is below: an untouched, unrelated
     retroknowledge-bearing library already leaves THIS digest
     unchanged (only a CHANGE to one forces a mismatch), so the
     remaining imprecision here is far narrower than the per-id one
     [or1]/[or2] exist to close. *)
  let live_closure_list =
    DirPath.Map.bindings current_libs
    |> List.map (fun (dp, { req_digest; req_iface; _ }) -> (dp, req_digest, req_iface))
  in
  let _, actual_closure_none_digest = flatten_closure live_closure_list in
  let check current (id, required, required_iface, required_objects_digest,
                      required_univs_digest, required_vernac_iface,
                      required_closure_names, required_closure_none_digest) =
    match DirPath.Map.find_opt id current with
  | None ->
    CErrors.user_err Pp.(pr_sequence str ["Reference to unknown module"; DirPath.to_string id; "."])
  | Some { req_root; req_digest = actual; req_iface = actual_iface;
           req_objects_digest = actual_objects_digest;
           req_univs_digest = actual_univs_digest;
           req_vernac_iface = actual_vernac_iface } ->
    (* Fast path: the dependency is byte-identical to what this library was
       compiled against. Fallback (see [dep_ok]): the dependency changed,
       but everything this dependent could have observed through it --
       its recorded [iface_table] subset, its exact-equality objects
       digest, its [(comp_univs, comp_sorts)] digest, its keyed
       vernac_iface subset, and the absence of a G7 closure-wide name
       collision (round 5) -- still matches the dependency's current
       state, so the dependent's own precompiled terms remain well-typed
       in the new environment. NEVER used by coqchk: see
       [check_required_strict]. *)
    (* binary-equivalence-taiga#841 round 7 (or1/or2): scope the LIVE
       per-id closure table to exactly the [DirPath.t]s the DEPENDENT's
       OWN recorded closure named, looked up fresh in [current] (the
       SAME live map every other check here already uses) -- not every
       library the CONSUMING process happens to have loaded elsewhere
       (the previous, globally-scoped [live_closure_list] above). An
       unrelated library loaded earlier in THIS SAME process (for an
       entirely different root [Require]) that happens to share a bare
       [Id.t] with something in [required_closure_names] is invisible to
       THIS dependent's own fresh compile (it never requires that
       library), so it must stay invisible here too -- the old,
       globally-scoped version refused reuse purely because of WHAT ELSE
       the consuming file happened to import, and in what order, never
       because of anything about the dependent itself. A [dp] recorded
       at compile time that is no longer loaded at all is simply dropped
       from the live side here, same as any other declaration that
       "vanished" -- [closure_subset_ok] already refuses that case on
       its own. *)
    let recorded_dps =
      Array.fold_left (fun s (dp, _, _) -> DirPath.Set.add dp s)
        DirPath.Set.empty required_closure_names
    in
    let scoped_live_list =
      DirPath.Set.fold (fun dp acc ->
          match DirPath.Map.find_opt dp current with
          | Some { req_digest; req_iface; _ } -> (dp, req_digest, req_iface) :: acc
          | None -> acc)
        recorded_dps []
    in
    let actual_closure_names, _ = flatten_closure scoped_live_list in
    if not (dep_ok ~actual ~required ~actual_iface ~required_iface
              ~actual_objects_digest ~required_objects_digest
              ~actual_univs_digest ~required_univs_digest
              ~actual_vernac_iface ~required_vernac_iface
              ~actual_closure_names ~required_closure_names
              ~actual_closure_none_digest ~required_closure_none_digest) then
      CErrors.user_err Pp.(pr_sequence str
        ["Inconsistent assumptions over module"; DirPath.to_string id; "."])
    else if req_root then
      (* the library is being transitively required, not a root anymore *)
      DirPath.Map.set id { req_root = false; req_digest = actual;
                            req_iface = actual_iface;
                            req_objects_digest = actual_objects_digest;
                            req_univs_digest = actual_univs_digest;
                            req_vernac_iface = actual_vernac_iface } current
    else
      (* nothing to do *)
      current
  in
  Array.fold_left check current_libs needed

(** The original, pre-fork digest-only check: no fallback branch exists in
    this function at all (not merely unreached -- there is nothing here for
    a future edit to accidentally re-enable). This is the ONLY check
    [checker/safe_checking.ml] may call (via [import_strict] below); its
    behavior against any tree is byte-for-byte what Rocq did before this
    fork existed, which is the entire soundness argument for coqchk: see
    binary-equivalence-taiga#841 "D2". *)
let check_required_strict current_libs needed =
  let check current (id, required, _required_iface, _required_objects_digest,
                      _required_univs_digest, _required_vernac_iface,
                      _required_closure_names, _required_closure_none_digest) =
    match DirPath.Map.find_opt id current with
  | None ->
    CErrors.user_err Pp.(pr_sequence str ["Reference to unknown module"; DirPath.to_string id; "."])
  | Some { req_root; req_digest = actual; req_iface = actual_iface;
           req_objects_digest = actual_objects_digest;
           req_univs_digest = actual_univs_digest;
           req_vernac_iface = actual_vernac_iface } ->
    if not (digest_match ~actual ~required) then
      CErrors.user_err Pp.(pr_sequence str
        ["Inconsistent assumptions over module"; DirPath.to_string id; "."])
    else if req_root then
      DirPath.Map.set id { req_root = false; req_digest = actual;
                            req_iface = actual_iface;
                            req_objects_digest = actual_objects_digest;
                            req_univs_digest = actual_univs_digest;
                            req_vernac_iface = actual_vernac_iface } current
    else
      current
  in
  Array.fold_left check current_libs needed


(** When loading a library, the current flags should match
    those needed for the library *)

let check_flags_for_library lib senv =
  let { rewrite_rules_allowed } = lib.comp_flags in
  set_rewrite_rules_allowed rewrite_rules_allowed senv

(** {6 Insertion of section variables} *)

(** They are now typed before being added to the environment.
    Same as push_named, but check that the variable is not already
    there. Should *not* be done in Environ because tactics add temporary
    hypothesis many many times, and the check performed here would
    cost too much. *)

let safe_push_named d env =
  let id = NamedDecl.get_id d in
  let _ =
    try
      let _ = Environ.lookup_named id env in
      CErrors.user_err Pp.(pr_sequence str ["Identifier"; Id.to_string id; "already defined."])
    with Not_found -> () in
  Environ.push_named d env

let push_named_def (id,de) senv =
  let sections = get_section senv.sections in
  let c, r, typ = Constant_typing.infer_local_def senv.env id de in
  let d = LocalDef (Context.make_annot id r, c, typ) in
  let env'' = safe_push_named d senv.env in
  let sections = Section.push_local d sections in
  { senv with sections=Some sections; env = env'' }

let push_named_assum (x,t) senv =
  let sections = get_section senv.sections in
  let t, r = Constant_typing.infer_local_assum senv.env t in
  let d = LocalAssum (Context.make_annot x r, t) in
  let sections = Section.push_local d sections in
  let env'' = safe_push_named d senv.env in
  { senv with sections=Some sections; env = env'' }

let push_section_context uctx senv =
  let sections = get_section senv.sections in
  let sections = Section.push_local_universe_context uctx sections in
  let senv = { senv with sections=Some sections } in
  let qctx, ctx = UVars.UContext.to_context_set uctx in
  let check_quality q =
    Sorts.QVar.is_global q &&
    not (QGraph.is_declared (Sorts.Quality.QVar q) (Environ.qualities senv.env))
  in
  let () = assert (Sorts.QVar.Set.for_all check_quality (fst qctx)) in
  let check_fresh u = match UGraph.check_declared_universes (Environ.universes senv.env) (Univ.Level.Set.singleton u) with
  | Result.Ok _ -> assert false
  | Result.Error _ -> ()
  in
  let () = Univ.Level.Set.iter check_fresh (fst ctx) in
  let env = Environ.push_context_set ~strict:false ctx senv.env in
  (* FIXME: check validity of the sort context *)
  (* FIXME: marking the section-local sorts as rigid makes little sense *)
  let env = Environ.push_qualities ~rigid:true qctx env in
  { senv with
    env;
    univ = Univ.ContextSet.union ctx senv.univ ;
    qualities = Sorts.QContextSet.union qctx senv.qualities }

(** {6 Insertion of new declarations to current environment } *)

let labels_of_mib mib =
  let add,get =
    let labels = ref Id.Set.empty in
    (fun id -> labels := Id.Set.add id !labels),
    (fun () -> !labels)
  in
  let visit_mip mip =
    add mip.mind_typename;
    Array.iter add mip.mind_consnames
  in
  Array.iter visit_mip mib.mind_packets;
  get ()

let add_retroknowledge pttc senv =
  { senv with
    env = Primred.add_retroknowledge senv.env pttc;
    local_retroknowledge = pttc::senv.local_retroknowledge }

(** A generic function for adding a new field in a same environment.
    It also performs the corresponding [add_constraints]. *)

type generic_name =
  | C of Constant.t
  | I of MutInd.t
  | R
  | M of ModPath.t
  | MT of ModPath.t

let add_field ((l,sfb) as field) gn senv =
  let mlabs,olabs = match sfb with
    | SFBmind mib ->
      let l = labels_of_mib mib in
      check_objlabels l senv; (Id.Set.empty,l)
    | SFBconst _ | SFBrules _ ->
      check_objlabel l senv; (Id.Set.empty, Id.Set.singleton l)
    | SFBmodule _ | SFBmodtype _ ->
      check_modlabel l senv; (Id.Set.singleton l, Id.Set.empty)
  in
  let env' = match sfb, gn with
    | SFBconst cb, C con -> Environ.add_constant con cb senv.env
    | SFBmind mib, I mind -> Environ.add_mind mind mib senv.env
    | SFBmodtype mtb, MT mp -> Environ.add_modtype mp mtb senv.env
    | SFBmodule mb, M mp -> Modops.add_module mp mb senv.env
    | SFBrules r, R -> Environ.add_rewrite_rules r.rewrules_rules senv.env
    | _ -> assert false
  in
  let sections = match senv.sections with
    | None -> None
    | Some sections ->
      match sfb, gn with
      | SFBconst cb, C con ->
        let poly = Declareops.constant_is_polymorphic cb in
        Some Section.(push_global ~poly env' (SecDefinition con) sections)
      | SFBmind mib, I mind ->
        let poly = Declareops.inductive_is_polymorphic mib in
        Some Section.(push_global ~poly env' (SecInductive mind) sections)
      | _, (M _ | MT _) -> Some sections
      | _ -> assert false
  in
  { senv with
    env = env';
    sections;
    revstruct = field :: senv.revstruct;
    modlabels = Id.Set.union mlabs senv.modlabels;
    objlabels = Id.Set.union olabs senv.objlabels }

(** Applying a certain function to the resolver of a safe environment *)

let update_resolver f senv = { senv with modresolver = f senv.modresolver }

type exported_opaque = {
  exp_handle : Opaqueproof.opaque_handle;
  exp_body : Constr.t;
  exp_univs : (int * int) option;
  (* Minimal amount of data needed to rebuild the private universes. We enforce
     in the API that private constants have no internal constraints. *)
}
type exported_private_constant = Constant.t * exported_opaque option

let repr_exported_opaque o =
  let priv = match o .exp_univs with
  | None -> Opaqueproof.PrivateMonomorphic ()
  | Some _ -> Opaqueproof.PrivatePolymorphic Univ.ContextSet.empty
  in
  (o.exp_handle, (o.exp_body, priv))

let set_vm_library lib senv =
  { senv with env = Environ.set_vm_library lib senv.env }

let push_const_bytecode senv cb =
  let vmtab, code = push_bytecode (Environ.vm_library senv.env) cb.const_body_code in
  let cb = { cb with const_body_code = code } in
  let senv = set_vm_library vmtab senv in
  senv, cb

let make_hbody = function
  | None -> None
  | Some hc -> Some (fun c ->
      assert (c == HConstr.self hc);
      snd @@ HConstr.hcons hc)

let add_constant_aux senv ?hbody (kn, cb) =
  let l = Constant.label kn in
  (* This is the only place where we hashcons the contents of a constant body *)
  let senv, cb = push_const_bytecode senv cb in
  let cb = if sections_are_opened senv then cb else
      Declareops.hcons_const_body ?hbody:(make_hbody hbody) cb
  in
  let senv' = add_field (l,SFBconst cb) (C kn) senv in
  let senv'' = match cb.const_body with
    | Undef (Some lev) ->
      update_resolver
        (Mod_subst.add_inline_delta_resolver (Constant.user kn) (lev,None)) senv'
    | _ -> senv'
  in
  senv''

let inline_side_effects env body side_eff =
  let open Constr in
  (** First step: remove the constants that are still in the environment *)
  let filter e =
    if Environ.mem_constant e.seff_constant env then None
    else Some e
  in
  (* CAVEAT: we assure that most recent effects come first *)
  let side_eff = List.map_filter filter (SideEffects.repr side_eff) in
  let sigs = List.rev_map (fun e -> e.seff_constant, e.seff_certif) side_eff in
  (** Most recent side-effects first in side_eff *)
  if List.is_empty side_eff then (body, Univ.ContextSet.empty, sigs, 0)
  else
    (** Second step: compute the lifts and substitutions to apply *)
    let cname c r = Context.make_annot (Name (Constant.label c)) r in
    let fold (subst, var, ctx, args) { seff_constant = c; seff_body = (_hbody, cb); seff_univs = univs; _ } =
      let (b, opaque) = match cb.const_body with
      | Def b -> (b, false)
      | OpaqueDef b -> (b, true)
      | _ -> assert false
      in
      match cb.const_universes with
      | Monomorphic ->
        (** Abstract over the term at the top of the proof *)
        let ty = cb.const_type in
        let subst = Cmap_env.add c (Inr var) subst in
        let ctx = Univ.ContextSet.union ctx univs in
        (subst, var + 1, ctx, (cname c cb.const_relevance, b, ty, opaque) :: args)
      | Polymorphic _ ->
        let () = assert (Univ.ContextSet.is_empty univs) in
        (** Inline the term to emulate universe polymorphism *)
        let subst = Cmap_env.add c (Inl b) subst in
        (subst, var, ctx, args)
    in
    let (subst, len, ctx, args) = List.fold_left fold (Cmap_env.empty, 1, Univ.ContextSet.empty, []) side_eff in
    (** Third step: inline the definitions *)
    let rec subst_const i k t = match Constr.kind t with
    | Const (c, u) ->
      let data = try Some (Cmap_env.find c subst) with Not_found -> None in
      begin match data with
      | None -> t
      | Some (Inl b) ->
        (** [b] is closed but may refer to other constants *)
        subst_const i k (Vars.subst_instance_constr u b)
      | Some (Inr n) ->
        mkRel (k + n - i)
      end
    | Rel n ->
      (** Lift free rel variables *)
      if n <= k then t
      else mkRel (n + len - i - 1)
    | _ -> Constr.map_with_binders ((+) 1) (fun k t -> subst_const i k t) k t
    in
    let map_args i (na, b, ty, opaque) =
      (** Both the type and the body may mention other constants *)
      let ty = subst_const (len - i - 1) 0 ty in
      let b = subst_const (len - i - 1) 0 b in
      (na, b, ty, opaque)
    in
    let args = List.mapi map_args args in
    let body = subst_const 0 0 body in
    let fold_arg (na, b, ty, opaque) accu =
      if opaque then mkApp (mkLambda (na, ty, accu), [|b|])
      else mkLetIn (na, b, ty, accu)
    in
    let body = List.fold_right fold_arg args body in
    (body, ctx, sigs, len - 1)

let inline_private_constants env ((body, ctx), side_eff) =
  let body, ctx', _, _ = inline_side_effects env body side_eff in
  let ctx' = Univ.ContextSet.union ctx ctx' in
  (body, ctx')

let warn_failed_cert = CWarnings.create ~name:"failed-abstract-certificate"
    ~category:CWarnings.CoreCategories.tactics ~default:CWarnings.AsError
    Pp.(fun kn ->
        str "Certificate for private constant " ++
        Id.print (Constant.label kn) ++
        str " failed.")

(* Given the list of signatures of side effects, checks if they match.
 * I.e. if they are ordered descendants of an ancestor of the current revstruct.
   Returns the universes needed to trust the side effects (None if they can't be trusted). *)
let check_signatures senv sl =
  match sl with
  | [] -> Ok Univ.ContextSet.empty
  | (firstkn,first) :: rest ->
    match CEphemeron.get first with
    | exception CEphemeron.InvalidKey -> Error None
    | first ->
    if not (Certificate.compatible senv first) then Error (Some firstkn)
    else
      let is_direct_ancestor curmb (kn, mb) =
        match CEphemeron.get mb with
        | exception CEphemeron.InvalidKey -> Error None
        | mb ->
          let mb = Certificate.safe_extend ~src:curmb ~dst:mb in
          match mb with
          | None -> Error (Some kn)
          | Some mb -> Ok mb
      in
      let accu = List.fold_left_error is_direct_ancestor first rest in
      match accu with
      | Error _ as e -> e
      | Ok mb ->
        let univs = Certificate.universes mb in
        Ok (Univ.ContextSet.diff univs senv.univ)

let check_signatures senv sl =
  match check_signatures senv sl with
  | Ok univs -> Some univs
  | Error None ->
    (* don't warn when the issue is an invalid ephemeron *)
    None
  | Error (Some kn) -> warn_failed_cert kn; None

type side_effect_declaration =
| DefinitionEff : Entries.definition_entry -> side_effect_declaration
| OpaqueEff : Constr.constr Entries.opaque_entry -> side_effect_declaration

let constant_entry_of_side_effect eff =
  let (_hbody, cb) = eff.seff_body in
  let open Entries in
  let univs =
    match cb.const_universes with
    | Monomorphic ->
      Monomorphic_entry
    | Polymorphic auctx ->
      Polymorphic_entry (UVars.AbstractContext.repr auctx)
  in
  let p =
    match cb.const_body with
    | OpaqueDef b -> b
    | Def b -> b
    | _ -> assert false in
  if Declareops.is_opaque cb then
  OpaqueEff {
    opaque_entry_body = p;
    opaque_entry_secctx = Context.Named.to_vars cb.const_hyps;
    opaque_entry_type = cb.const_type;
    opaque_entry_universes = univs;
  }
  else
  DefinitionEff {
    definition_entry_body = p;
    definition_entry_secctx = Some (Context.Named.to_vars cb.const_hyps);
    definition_entry_type = Some cb.const_type;
    definition_entry_universes = univs;
    definition_entry_inline_code = cb.const_inline_code }

let export_eff eff =
  (eff.seff_constant, eff.seff_body)

let is_empty_private = function
| Opaqueproof.PrivateMonomorphic ctx -> Univ.ContextSet.is_empty ctx
| Opaqueproof.PrivatePolymorphic ctx -> Univ.ContextSet.is_empty ctx

let compile_bytecode env cb =
  let code = Vmbytegen.compile_constant_body ~fail_on_error:false env cb.const_universes cb.const_body in
  { cb with const_body_code = code }

(* Special function to call when the body of an opaque definition is provided.
  It performs the type-checking of the body immediately. *)
let infer_direct_opaque ~sec_univs env ce =
  let cb, ctx = Constant_typing.infer_opaque ~sec_univs env ce in
  let body = ce.Entries.opaque_entry_body, Univ.ContextSet.empty in
  let handle _env c () = (c, Univ.ContextSet.empty, 0) in
  let (hbody, c, u) = Constant_typing.check_delayed handle ctx (body, ()) in
  (* No constraints can be generated, we set it empty everywhere *)
  let () = assert (is_empty_private u) in
  hbody, { cb with const_body = OpaqueDef c }

let export_side_effects senv eff =
  let sec_univs = Option.map Section.all_poly_univs senv.sections in
  let env = senv.env in
  let not_exists e = not (Environ.mem_constant e.seff_constant env) in
  let aux (acc,sl) e =
    if not (not_exists e) then acc, sl
    else e :: acc, (e.seff_constant, e.seff_certif) :: sl in
  let seff, signatures = List.fold_left aux ([],[]) (SideEffects.repr eff) in
  let trusted = check_signatures senv signatures in
  let push_seff env eff =
    let { seff_constant = kn; seff_body = (_hbody, cb); _ } = eff in
    let vmtab, code = push_bytecode (Environ.vm_library env) cb.const_body_code in
    let env = Environ.set_vm_library vmtab env in
    let cb = { cb with const_body_code = code } in
    let env = Environ.add_constant kn (lift_constant cb) env in
    env
  in
  match trusted with
  | Some univs ->
    univs, List.map export_eff seff
  | None ->
    let rec recheck_seff seff univs acc env = match seff with
      | [] -> univs, List.rev acc
      | eff :: rest ->
        let uctx = eff.seff_univs in
        let env = Environ.push_context_set ~strict:true uctx env in
        let univs = Univ.ContextSet.union uctx univs in
        let env, cb =
          let ce = constant_entry_of_side_effect eff in
          let hbody, cb = match ce with
            | DefinitionEff ce ->
              Constant_typing.infer_definition ~sec_univs env ce
            | OpaqueEff ce ->
              infer_direct_opaque ~sec_univs env ce
          in
          let cb = compile_bytecode env cb in
          let eff = { eff with seff_body = (hbody, cb) } in
          (push_seff env eff, export_eff eff)
        in
        recheck_seff rest univs (cb :: acc) env
    in
    recheck_seff seff Univ.ContextSet.empty [] env

let push_opaque_proof senv =
  let o, otab = Opaqueproof.create (library_dp_of_senv senv) senv.opaquetab in
  let senv = { senv with opaquetab = otab } in
  senv, o

let export_private_constants eff senv =
  let uctx, exported = export_side_effects senv eff in
  let senv = push_context_set ~strict:true uctx senv in
  let map senv (kn, (hbody, c)) = match c.const_body with
  | OpaqueDef body ->
    (* Don't care about the body, it has been checked by {!infer_direct_opaque} *)
    let senv, o = push_opaque_proof senv in
    let (_, _, _, h) = Opaqueproof.repr o in
    let univs = match c.const_universes with
    | Monomorphic -> None
    | Polymorphic auctx -> Some (UVars.AbstractContext.size auctx)
    in
    (* Hashcons now, before storing in the opaque table *)
    let _, body = match hbody with
    | None -> Constr.hcons body
    | Some hbody ->
      let () = assert (HConstr.self hbody == body) in
      HConstr.hcons hbody
    in
    let opaque = { exp_body = body; exp_handle = h; exp_univs = univs } in
    senv, (kn, { c with const_body = OpaqueDef o }, Some opaque, None)
  | Def _ | Undef _ | Primitive _ | Symbol _ as body ->
    (* Hashconsing is handled by {!add_constant_aux}, propagate hbody *)
    senv, (kn, { c with const_body = body }, None, hbody)
  in
  let senv, bodies = List.fold_left_map map senv exported in
  let exported = List.map (fun (kn, _, opaque, _) -> kn, opaque) bodies in
  (* No delayed constants to declare *)
  let fold senv (kn, cb, _, hbody) = add_constant_aux ?hbody senv (kn, cb) in
  let senv = List.fold_left fold senv bodies in
  exported, senv

let add_constant l decl senv =
  let kn = Constant.make2 senv.modpath l in
  let senv, (hbody, cb) =
    let sec_univs = Option.map Section.all_poly_univs senv.sections in
      match decl with
      | Entries.OpaqueEntry ce ->
        let senv, o = push_opaque_proof senv in
        let cb, ctx = Constant_typing.infer_opaque ~sec_univs senv.env ce in
        (* Push the delayed data in the environment *)
        let (_, _, _, i) = Opaqueproof.repr o in
        let nonce = Nonce.create () in
        let future_cst = HandleMap.add i (ctx, senv, nonce) senv.future_cst in
        let senv = { senv with future_cst } in
        senv, (None, { cb with const_body = OpaqueDef o })
      | Entries.DefinitionEntry entry ->
        senv, Constant_typing.infer_definition ~sec_univs senv.env entry
      | Entries.ParameterEntry entry ->
        senv, (None, Constant_typing.infer_parameter ~sec_univs senv.env entry)
      | Entries.PrimitiveEntry entry ->
        let senv = match entry with
        | { Entries.prim_entry_content = CPrimitives.OT_type t; _ } ->
          if sections_are_opened senv then CErrors.anomaly (Pp.str "Primitive type not allowed in sections");
          add_retroknowledge (Retroknowledge.Register_type(t,kn)) senv
        | _ -> senv in
        senv, (None, Constant_typing.infer_primitive senv.env entry)
      | Entries.SymbolEntry entry ->
        senv, (None, Constant_typing.infer_symbol senv.env entry)
  in
  let cb = compile_bytecode senv.env cb in
  let senv = add_constant_aux senv ?hbody (kn, cb) in
  kn, senv

let add_constant ?typing_flags l decl senv =
  with_typing_flags ?typing_flags senv ~f:(add_constant l decl)

type opaque_certificate = {
  opq_body : Constr.t;
  opq_univs : Univ.ContextSet.t Opaqueproof.delayed_universes;
  opq_handle : Opaqueproof.opaque_handle;
  opq_nonce : Nonce.t;
}

let check_opaque senv (i : Opaqueproof.opaque_handle) pf =
  let ty_ctx, trust, nonce =
    try HandleMap.find i senv.future_cst
    with Not_found ->
      CErrors.anomaly Pp.(str "Missing opaque with identifier " ++ int (Opaqueproof.repr_handle i))
  in
  let handle env body eff =
    let body, uctx, signatures, skip = inline_side_effects env body eff in
    let trusted = check_signatures trust signatures in
    let trusted, uctx = match trusted with
    | None -> 0, uctx
    | Some univs -> skip, Univ.ContextSet.union univs uctx
    in
    body, uctx, trusted
  in
  let (hbody, c, ctx) = Constant_typing.check_delayed handle ty_ctx pf in
  let _, c = match hbody with
    | Some hbody -> assert (c == HConstr.self hbody); HConstr.hcons hbody
    | None -> Constr.hcons c
  in
  let ctx = match ctx with
  | Opaqueproof.PrivateMonomorphic u ->
    Opaqueproof.PrivateMonomorphic (snd @@ Univ.ContextSet.hcons u)
  | Opaqueproof.PrivatePolymorphic u ->
    Opaqueproof.PrivatePolymorphic (snd @@ Univ.ContextSet.hcons u)
  in
  { opq_body = c; opq_univs = ctx; opq_handle = i; opq_nonce = nonce }

let fill_opaque { opq_univs = ctx; opq_handle = i; opq_nonce = n; _ } senv =
  let () = if not @@ HandleMap.mem i senv.future_cst then
    CErrors.anomaly Pp.(str "Missing opaque handle" ++ spc () ++ int (Opaqueproof.repr_handle i))
  in
  let _, _, nonce = HandleMap.find i senv.future_cst in
  let () =
    if not (Nonce.equal n nonce) then
      CErrors.anomaly  Pp.(str "Invalid opaque certificate")
  in
  (* TODO: Drop the the monomorphic constraints, they should really be internal
     but the higher levels use them haphazardly. *)
  let senv = match ctx with
  | Opaqueproof.PrivateMonomorphic ctx -> push_context_set ~strict:true ctx senv
  | Opaqueproof.PrivatePolymorphic _ -> senv
  in
  (* Mark the constant as having been checked *)
  { senv with future_cst = HandleMap.remove i senv.future_cst }

let is_filled_opaque i senv =
  let () = assert (Opaqueproof.mem_handle i senv.opaquetab) in
  not (HandleMap.mem i senv.future_cst)

let repr_certificate { opq_body = body; opq_univs = ctx; _ } =
  body, ctx

let check_constraints uctx = function
| Entries.Polymorphic_entry _ -> Univ.ContextSet.is_empty uctx
| Entries.Monomorphic_entry -> true

let add_private_constant l uctx decl senv : (Constant.t * private_constants) * safe_environment =
  let kn = Constant.make2 senv.modpath l in
  let senv = push_context_set ~strict:true uctx senv in
    let hbody, cb =
      let sec_univs = Option.map Section.all_poly_univs senv.sections in
      match decl with
      | OpaqueEff ce ->
        let () = assert (check_constraints uctx ce.Entries.opaque_entry_universes) in
        infer_direct_opaque ~sec_univs senv.env ce
      | DefinitionEff ce ->
        let () = assert (check_constraints uctx ce.Entries.definition_entry_universes) in
        Constant_typing.infer_definition ~sec_univs senv.env ce
    in
  let cb = compile_bytecode senv.env cb in
  let dcb = match cb.const_body with
  | Def _ as const_body -> { cb with const_body }
  | OpaqueDef _ ->
    (* We drop the body, to save the definition of an opaque and thus its
       hashconsing. It does not matter since this only happens inside a proof,
       and depending of the opaque status of the latter, this proof term will be
       either inlined or reexported. *)
    { cb with const_body = Undef None }
  | Undef _ | Primitive _ | Symbol _ -> assert false
  in
  let senv = add_constant_aux senv ?hbody (kn, dcb) in
  let eff =
    let from_env = CEphemeron.create (Certificate.make senv) in
    let eff = {
      seff_certif = from_env;
      seff_constant = kn;
      seff_body = (hbody, cb);
      seff_univs = uctx;
    } in
    SideEffects.add eff empty_private_constants
  in
  (kn, eff), senv

(** Rewrite rules *)

let add_rewrite_rules l rules senv =
  if Option.has_some senv.sections
  then CErrors.user_err Pp.(str "Adding rewrite rules not supported in sections.");
  (* TODO: Hashconsing? *)
  add_field (l, SFBrules rules) R senv

(** Insertion of inductive types *)

let check_mind mie lab =
  let open Entries in
  match mie.mind_entry_inds with
  | [] -> assert false (* empty inductive entry *)
  | oie::_ ->
    (* The label and the first inductive type name should match *)
    assert (Id.equal lab oie.mind_entry_typename)

let add_checked_mind kn mib senv =
  let mib =
    match mib.mind_hyps with [] -> Declareops.hcons_mind mib | _ -> mib
  in
  add_field (MutInd.label kn,SFBmind mib) (I kn) senv

let add_mind l mie senv =
  let () = check_mind mie l in
  let kn = MutInd.make2 senv.modpath l in
  let sec_univs = Option.map Section.all_poly_univs senv.sections in
  let mib, why_not_prim_record = Indtypes.check_inductive senv.env ~sec_univs kn mie in
  (* We still have to add the template monomorphic constraints, and only those
     ones. In all other cases, they are already part of the environment at this
     point. *)
  let senv = match mib.mind_template with
  | None -> senv
  | Some { template_context = ctx; template_defaults = u; _ } ->
    let qs, levels = UVars.Instance.levels u in
    let () = assert (Sorts.Quality.Set.for_all (fun q -> Sorts.Quality.equal Sorts.Quality.qtype q) qs) in
    let (qctx, uctx) = UVars.AbstractContext.instantiate u ctx in
    let () = assert (Sorts.ElimConstraints.is_empty qctx) in
    (* Eliminiation constraints used to be pushed with QGraph.Static *)
    let senv = push_context_set ~strict:true (levels, uctx) senv in
    senv
  in
  (kn, why_not_prim_record), add_checked_mind kn mib senv

let add_mind ?typing_flags l mie senv =
  with_typing_flags ?typing_flags senv ~f:(add_mind l mie)

(** Insertion of module types *)

let check_state senv =
  (Environ.universes senv.env, Conversion.checked_universes)

let vm_handler env univs c vmtab =
  let env = Environ.set_vm_library vmtab env in
  let code = Vmbytegen.compile_constant_body ~fail_on_error:false env univs (Def c) in
  let vmtab, code = push_bytecode vmtab code in
  vmtab, code

let vm_state senv =
  (Environ.vm_library senv.env, { Mod_typing.vm_handler })

let add_modtype l params_mte inl senv =
  let mp = MPdot(senv.modpath, l) in
  let state = check_state senv in
  let vmstate = vm_state senv in
  let mtb, _, vmtab = Mod_typing.translate_modtype state vmstate senv.env mp inl params_mte  in
  let senv = set_vm_library vmtab senv in
  let mtb = Mod_declarations.hcons_module_type mtb in
  let senv = add_field (l,SFBmodtype mtb) (MT mp) senv in
  mp, senv

(** full_add_module adds module with universes and constraints *)

let full_add_module mp mb senv =
  let dp = ModPath.dp mp in
  let linkinfo = Nativecode.link_info_of_dirpath dp in
  { senv with env = Modops.add_linked_module mp mb linkinfo senv.env }

(** Insertion of modules *)

let add_module l me inl senv =
  let mp = MPdot(senv.modpath, l) in
  let state = check_state senv in
  let vmstate = vm_state senv in
  let mb, _, vmtab = Mod_typing.translate_module state vmstate senv.env mp inl me in
  let senv = set_vm_library vmtab senv in
  let mb = Mod_declarations.hcons_module_body mb in
  let senv = add_field (l,SFBmodule mb) (M mp) senv in
  let senv = match mod_global_delta mb with
  | None -> senv
  | Some delta -> update_resolver (Mod_subst.add_delta_resolver delta) senv
  in
  (mp, mod_delta mb), senv

(** {6 Starting / ending interactive modules and module types } *)

let start_mod_modtype ~istype l senv =
  let () = check_modlabel l senv in
  let () = check_empty_context senv in
  let mp = MPdot(senv.modpath, l) in
  mp,
  {
    (* modified fields *)
    modpath = mp;
    modvariant = if istype then SIG ([], senv) else STRUCT ([],senv);

    (* carried over fields *)
    env = senv.env;
    future_cst = senv.future_cst;
    modresolver = Mod_subst.empty_delta_resolver mp;
    paramresolver = ParamResolver.add_delta_resolver senv.modpath senv.modresolver senv.paramresolver;
    univ = senv.univ;
    qualities = senv.qualities;
    required = senv.required;
    opaquetab = senv.opaquetab;
    sections = None; (* checked in check_empty_context *)

    (* module local fields *)
    revstruct = [];
    modlabels = Id.Set.empty;
    objlabels = Id.Set.empty;
    loads = [];
    local_retroknowledge = [];
  }

let start_module l senv = start_mod_modtype ~istype:false l senv

let start_modtype l senv = start_mod_modtype ~istype:true l senv

(** Adding parameters to the current module or module type.
    This module should have been freshly started. *)

let add_module_parameter mbid mte inl senv =
  let () = check_empty_struct senv in
  let mp = MPbound mbid in
  let state = check_state senv in
  let vmstate = vm_state senv in
  let mtb, _, vmtab = Mod_typing.translate_modtype state vmstate senv.env mp inl ([],mte) in
  let senv = set_vm_library vmtab senv in
  let senv = { senv with env = Modops.add_module_parameter mbid mtb senv.env } in
  let new_variant = match senv.modvariant with
    | STRUCT (params,oldenv) -> STRUCT ((mbid,mtb) :: params, oldenv)
    | SIG (params,oldenv) -> SIG ((mbid,mtb) :: params, oldenv)
    | _ -> assert false
  in
  let new_paramresolver = match mod_global_delta mtb with
  | None -> senv.paramresolver
  | Some delta -> ParamResolver.add_delta_resolver mp delta senv.paramresolver
  in
  mtb,
  { senv with
    modvariant = new_variant;
    paramresolver = new_paramresolver }

let rec module_num_parameters senv =
  match senv.modvariant with
  | STRUCT (params,senv) -> List.length params :: module_num_parameters senv
  | SIG (params,senv) -> List.length params :: module_num_parameters senv
  | _ -> []

let rec module_is_modtype senv =
  match senv.modvariant with
  | STRUCT (_,senv) -> false :: module_is_modtype senv
  | SIG (_,senv) -> true :: module_is_modtype senv
  | _ -> []

let functorize params init =
  List.fold_left (fun e (mbid,mt) -> MoreFunctor(mbid,mt,e)) init params

let propagate_loads senv =
  List.fold_left
    (fun env (mp, mb) -> full_add_module mp mb env)
    senv
    (List.rev senv.loads)

(** Build the module body of the current module, taking in account
    a possible return type (_:T) *)

let build_module_body params restype senv =
  let struc = NoFunctor (List.rev senv.revstruct) in
  let restype' = Option.map (fun (ty,inl) -> (([],ty),inl)) restype in
  let state = check_state senv in
  let vmstate = vm_state senv in
  let mb, _, vmtab =
    Mod_typing.finalize_module state vmstate senv.env senv.modpath
      (struc, senv.modresolver) restype'
  in
  let senv = set_vm_library vmtab senv in
  let mb' = functorize_module params mb in
  set_retroknowledge mb' senv.local_retroknowledge

(** Returning back to the old pre-interactive-module environment,
    with one extra component and some updated fields
    (constraints, required, etc) *)

let allow_delayed_constants = ref false

let propagate_senv newdef newenv newresolver senv oldsenv =
  (* This asserts that after Paral-ITP, standard vo compilation is behaving
   * exctly as before: the same universe constraints are added to modules *)
  if not !allow_delayed_constants && not (HandleMap.is_empty senv.future_cst) then
    CErrors.anomaly ~label:"safe_typing"
      Pp.(str "True Future.t were created for opaque constants even if -async-proofs is off");
  { oldsenv with
    env = newenv;
    modresolver = newresolver;
    revstruct = newdef::oldsenv.revstruct;
    modlabels = Id.Set.add (fst newdef) oldsenv.modlabels;
    univ = senv.univ;
    qualities = senv.qualities ;
    future_cst = senv.future_cst;
    required = senv.required;
    loads = senv.loads@oldsenv.loads;
    local_retroknowledge =
      senv.local_retroknowledge@oldsenv.local_retroknowledge;
    opaquetab = senv.opaquetab;
  }

let end_module l restype senv =
  let mp = senv.modpath in
  let params, oldsenv = check_struct senv.modvariant in
  let () = check_current_label l mp in
  let () = check_empty_context senv in
  let mbids = List.rev_map fst params in
  let mb = build_module_body params restype senv in
  let newenv = Environ.set_universes (Environ.universes senv.env) oldsenv.env in
  let newenv = Environ.set_qualities (Environ.qualities senv.env) newenv in
  let newenv = if Environ.rewrite_rules_allowed senv.env then Environ.allow_rewrite_rules newenv else newenv in
  let newenv = Environ.set_vm_library (Environ.vm_library senv.env) newenv in
  let senv' = propagate_loads { senv with env = newenv } in
  let newenv = Modops.add_module mp mb senv'.env in
  let newresolver = match mod_global_delta mb with
  | None -> oldsenv.modresolver
  | Some delta -> Mod_subst.add_delta_resolver delta oldsenv.modresolver
  in
  (mp, mbids, mod_delta mb),
  propagate_senv (l,SFBmodule mb) newenv newresolver senv' oldsenv

let build_mtb = Mod_declarations.make_module_type

let end_modtype l senv =
  let mp = senv.modpath in
  let params, oldsenv = check_sig senv.modvariant in
  let () = check_current_label l mp in
  let () = check_empty_context senv in
  let mbids = List.rev_map fst params in
  let newenv = Environ.set_universes (Environ.universes senv.env) oldsenv.env in
  let newenv = if Environ.rewrite_rules_allowed senv.env then Environ.allow_rewrite_rules newenv else newenv in
  let newenv = Environ.set_vm_library (Environ.vm_library senv.env) newenv in
  let senv' = propagate_loads {senv with env=newenv} in
  let auto_tb = functorize params (NoFunctor (List.rev senv.revstruct)) in
  let mtb = build_mtb auto_tb senv.modresolver in
  let newenv = Environ.add_modtype mp mtb senv'.env in
  let newresolver = oldsenv.modresolver in
  (mp,mbids),
  propagate_senv (l,SFBmodtype mtb) newenv newresolver senv' oldsenv

(** {6 Inclusion of module or module type } *)

let add_include me is_module inl senv =
  let open Mod_typing in
  let mp_sup = senv.modpath in
  let state = check_state senv in
  let vmstate = vm_state senv in
  let sign,(),resolver, _, vmtab =
    translate_mse_include is_module state vmstate senv.env mp_sup inl me
  in
  let senv = set_vm_library vmtab senv in
  (* Include Self support  *)
  let struc = NoFunctor (List.rev senv.revstruct) in
  let mb = Mod_declarations.make_module_body struc senv.modresolver [] in
  let rec compute_sign sign resolver =
    match sign with
    | MoreFunctor(mbid,mtb,str) ->
      let state = check_state senv in
      (* Module subcomponents are already part of senv.env at this point *)
      let env = Environ.shallow_add_module mp_sup mb senv.env in
      let (_ : UGraph.t) = Subtyping.check_subtypes ~direct:true state env mp_sup (MPbound mbid) mtb in
      let mpsup_delta =
        Modops.inline_delta_resolver senv.env inl mp_sup mbid mtb senv.modresolver
      in
      let subst = Mod_subst.map_mbid mbid mp_sup mpsup_delta in
      let resolver = Mod_subst.subst_codom_delta_resolver subst resolver in
      compute_sign (Modops.subst_signature subst mp_sup str) resolver
    | NoFunctor str -> resolver, str
  in
  let resolver, str = compute_sign sign resolver in
  let senv = update_resolver (Mod_subst.add_delta_resolver resolver) senv in
  let add senv ((l,elem) as field) =
    let new_name = match elem with
      | SFBconst _ ->
        C (Mod_subst.constant_of_delta_kn resolver (KerName.make mp_sup l))
      | SFBmind _ ->
        I (Mod_subst.mind_of_delta_kn resolver (KerName.make mp_sup l))
      | SFBrules _ -> R
      | SFBmodule _ -> M (MPdot (mp_sup, l))
      | SFBmodtype _ -> MT (MPdot (mp_sup, l))
    in
    add_field field new_name senv
  in
  resolver, List.fold_left add senv str

(** {6 Libraries, i.e. compiled modules } *)

let dirpath_of_library lib = lib.comp_name

let module_of_library lib = lib.comp_mod
let replace_module_of_library lib mb = { lib with comp_mod = mb }
let iface_of_library lib = lib.comp_iface
let objects_digest_of_library lib = lib.comp_objects_digest
let univs_digest_of_library lib = lib.comp_univs_digest
let vernac_iface_of_library lib = lib.comp_vernac_iface
let closure_of_library lib = lib.comp_closure_names, lib.comp_closure_none_digest

let univs_of_library lib = lib.comp_sorts, lib.comp_univs

(** FIXME: MS: remove?*)
let current_modpath senv = senv.modpath
let current_dirpath senv = Names.ModPath.dp (current_modpath senv)

let start_library dir senv =
  (* When starting a library, the current environment should be initial
     i.e. only composed of Require's *)
  (* XXX is it really possible / should be allowed to have nonempty Requires?
     especially if [dir] is in the [senv.required] *)
  assert (is_initial senv);
  assert (not (DirPath.is_empty dir));
  let mp = MPfile dir in
  let vmtab = Vmlibrary.set_path dir (Environ.vm_library senv.env) in
  let env = Environ.set_vm_library vmtab senv.env in
  mp,
  { env = env;
    modpath = mp;
    modvariant = LIBRARY;
    required = senv.required;

    modresolver = Mod_subst.empty_delta_resolver mp;
    paramresolver = ParamResolver.empty dir;
    revstruct = [];
    modlabels = Id.Set.empty;
    objlabels = Id.Set.empty;
    sections = None;
    future_cst = HandleMap.empty;
    univ = Univ.ContextSet.empty;
    qualities = Sorts.QContextSet.empty;
    loads = [];
    local_retroknowledge = [];
    opaquetab = Opaqueproof.empty_opaquetab;
  }

(** Canonicalize a constant's body for interface-digest purposes. Both
    [Undef] ([Admitted], no body at all) and [OpaqueDef] (a [Qed]'d proof,
    stored as an opaque-table handle whose value is irrelevant here)
    collapse to the same nullary marker: a dependent can unfold neither
    one, so swapping one for the other -- the whole point of this cutoff
    -- must not perturb the digest. [Def]/[Primitive]/[Symbol] are kept
    as-is, since those bodies ARE visible to a dependent (conversion can
    unfold a transparent [Def]). *)
type canon_const_body =
  | CBNoBody
  | CBDef of Constr.t
  | CBPrimitive of CPrimitives.t
  | CBSymbol of bool

let canon_const_body (cb : constant_body) : canon_const_body =
  match cb.const_body with
  | Undef _ | OpaqueDef _ -> CBNoBody
  | Def v -> CBDef v
  | Primitive p -> CBPrimitive p
  | Symbol b -> CBSymbol b

(** binary-equivalence-taiga#841 (Lean attack-battery D3): [Csha256], not
    [Digest]/MD5, for every digest computed over bytes the AGENT fully
    controls (a constant/inductive's own type/body/universes) -- MD5
    collisions are a few seconds of attacker compute for a chosen-prefix
    construction, and this digest is the one thing [dep_ok]'s relaxed
    fallback trusts without re-verification (a REUSED dependent's own
    term is never re-typechecked on load, unlike a fresh compile). Bound:
    this remains dev-loop-only (never consulted by [check_required_strict]/
    coqchk, and the grade always recompiles the agent's own `.v` from
    scratch, never trusting a cached `.vo`), but Review841/Lean's round
    found that bound alone was treated as a reason not to fix an
    otherwise-practical attack, which is the wrong call once a free fix
    exists -- [Csha256.t] is a plain [string] like [Digest.t], so every
    comparison site ([Digest.equal]/[String.equal]/[Array.mem]) keeps
    working unchanged; only the computation changes. The stock
    whole-library [vodigest] (pre-fork Rocq's own file-identity digest,
    [digest_match] above) is UNCHANGED, deliberately out of this fork's
    scope -- see the module-level note on [Csha256] for why. *)
let iface_digest_of_const (cb : constant_body) : Digest.t =
  Csha256.digest (Marshal.to_string
    (cb.const_hyps, cb.const_univ_hyps, canon_const_body cb, cb.const_type,
     cb.const_relevance, cb.const_universes, cb.const_inline_code,
     cb.const_typing_flags)
    [])

(* Inductive declarations have no opaque component (constructors and
   eliminators are always fully transparent), so their whole body is part
   of the interface as-is. *)
let iface_digest_of_mind (mib : mutual_inductive_body) : Digest.t =
  Csha256.digest (Marshal.to_string mib [])

(** binary-equivalence-taiga#841 Review841 G7 round 5 (g7ctor): a
    constructor's own short name (e.g. [c] in [Inductive t := c | d]) was
    not previously a separate key in this table at all -- only the
    inductive TYPE's own label ([t]) was, so a dependency that added a
    new top-level declaration whose name collided with an EXISTING
    constructor's name (not the type's) was invisible to every reuse
    check that keys off this table. Fix: emit one entry per constructor,
    in addition to the type's own entry, all keyed to the SAME whole-mib
    digest (a constructor's identity is part of the mib as a whole, same
    as the type's).

    binary-equivalence-taiga#841 round 7 (g7mod): a label can also be a
    nested [Module], not just a leaf [SFBconst]/[SFBmind], and the
    PREDECESSOR of this function bailed the WHOLE library to [None] the
    moment it saw one, hiding every name nested inside it from the G7
    shadow check (see [flatten_closure]'s doc comment for why that is
    unsound: a name hidden this way can be shadowed by a LATER addition
    elsewhere with nothing to catch it). Fix: recurse into a nested
    module's own expanded signature ([mod_type], which already reflects
    any ascribed restriction -- [Module M : T. ... End M.] only exposes
    [T]'s labels, never the unrestricted body), collecting its
    [SFBconst]/[SFBmind] entries the SAME way as a top-level one.

    binary-equivalence-taiga#841 round 8 (kd1/kd2, Lean round 7 review):
    entries are keyed by the FULL QUALIFIED dotted path (e.g. [M.foo]),
    NOT the bare [Id.t] round 7 first shipped with. Round 7's bare-[Id.t]
    keying put a top-level [foo] and a nested [M.foo] in the SAME
    [iface_table] under the SAME key "foo" -- harmless for
    [closure_subset_ok] (grouped into a LIST per id, every [(dp, digest)]
    pair checked by existence, so duplicates are fine), but UNSOUND for
    [iface_subset_ok]: its single [Array.find_opt] returns only the
    FIRST "foo" it finds, so when the recorded table ALSO has two "foo"
    entries that started with the SAME digest (the common case: nothing
    forces a dependency's own declarations to differ from each other),
    checking the SECOND recorded entry against [live] silently compares
    it against the FIRST live entry instead -- if that first one is
    unchanged, the check wrongly PASSES even though the actual second
    declaration changed. Confirmed exploitable: a dependent that proved
    something from the nested declaration's value kept its [.vo] reused
    after ONLY the top-level, same-named declaration's value changed (or
    the reverse), producing a kernel-accepted proof of [False]. Keying by
    the full path makes every entry UNIQUE per library, so
    [Array.find_opt] always finds the one real match -- [iface_subset_ok]
    needs no other change. [flatten_closure] derives the bare basename
    back out of each qualified path only for ITS OWN per-[DirPath.t]
    shadow table, which is a DIFFERENT (deliberately coarser,
    cross-library) checked property.

    binary-equivalence-taiga#841 round 8 (mt1): a [Module Type]'s own
    fields (e.g. [Parameter x] in [Module Type T. Parameter x : nat. End
    T.]) are never real G7 shadow candidates -- a module type is never
    directly dereferenceable the way a module is (there is no [Import T.]
    for a module type) -- so folding their bare basenames into the SAME
    basename space as ordinary declarations produced spurious
    cross-library "collisions" (an unrelated library's harmless [Module
    Type] sharing a bare field name with a real declaration elsewhere
    wrongly refused every reuse of the library that defines it, the mt1
    shape).

    Round 8 shipped this by excluding [SFBmodtype] from [comp_iface]
    ENTIRELY ([SFBmodtype _ -> []]). That over-corrected: Review841 round
    8 (Lean round 8 review, issuecomment-6192580006) found it also
    removes a Module Type's fields from [comp_iface] itself, the table
    [iface_subset_ok] checks a library's OWN content against -- so a
    changed Module Type signature (a [Parameter]'s type, an [Axiom]'s
    statement) became invisible to the per-declaration subset check too,
    and a stale dependent that sealed a module against the old
    signature, declared a module of it, included it, or took it as a
    functor parameter was wrongly REUSED even though a fresh compile
    fails (mtc1/mtc3/mtc4/mtc5/mtc6/mtn1).

    Fix (round 9): recurse into [SFBmodtype] exactly like [SFBmodule]
    (same [mod_type]/[NoFunctor]/[MoreFunctor] cases, via the shared
    [entries_of_signature] below), so a Module Type's fields DO enter
    [comp_iface] -- closing mtc1-6/mtn1 -- and then mark every entry
    produced while recursing through a Module Type's structure with the
    reserved [modtype_entry_marker] prefix on its OWN basename (via
    [mark_basename]). A marked basename can never equal any real
    identifier's basename (same digit-leading trick as
    [opaque_entry_prefix]; see that constant's doc comment below), so
    [flatten_closure]'s shadow table -- which only ever compares entries
    by basename -- can never confuse a Module Type's abstract field with
    a same-named real declaration anywhere, preserving mt1/fuB/fuD/fu3's
    fix exactly. [comp_iface]/[iface_subset_ok] compare by the FULL
    qualified path, unaffected by the marker's presence or position.

    Two things remain genuinely unenumerable, and are NOT folded into the
    per-path table as an ordinary name: a rewrite-rules block ([SFBrules],
    which retargets an EXISTING [Constant.t] rather than naming a new
    one, so there is no candidate name to key an entry on) and an
    unapplied functor's own body (a nested module whose own [mod_type]
    is [MoreFunctor _] -- its parameter-dependent content has no fixed
    digest, and in any case nothing inside it is nameable from outside
    without first supplying an argument: there is no [F.x] syntax for an
    unapplied functor [F]; apply it to get a concrete module, whose OWN
    expanded signature is enumerated normally wherever THAT module is
    itself declared). Rather than bailing the WHOLE library to [None] for
    either case the way the pre-round-7 code did, fold the unenumerable
    chunk's own content digest into the SAME table under a synthetic key
    scoped to its exact qualified path ([opaque_entry_key]):
    [iface_subset_ok] already refuses whenever a recorded entry's digest
    changes or its key vanishes, which is exactly "this unenumerable
    chunk's content changed or disappeared" -- the SAME exact-match
    fallback the pre-round-7 whole-library [None] gave this chunk, now
    scoped to just the chunk instead of poisoning every ordinary,
    unrelated declaration sharing its library. *)
let opaque_entry_prefix = "0usage_cutoff_opaque_"
(** Reserved prefix for a synthetic FINAL SEGMENT standing in for a chunk
    of a library's structure that [iface_entries_of_sfb] cannot give a
    normal per-name digest ([SFBrules], or a nested module whose own
    [mod_type] is a [MoreFunctor]). Starts with a digit: Rocq's lexer
    classifies a digit as [IdentPart], never [Letter]/[IdentSep], so NO
    identifier the parser ever accepts can start with one
    ([Unicode.is_valid_ident_initial]) -- no real declaration's own
    basename, in this library or any other, can ever collide with a key
    built from this prefix. [opaque_entry_key] marks ONLY the final
    (innermost) segment, keeping any containing path intact, so
    [basename_of_qualified_path] -- which looks at the segment AFTER the
    last dot -- still returns a synthetic, uncollidable basename for a
    NESTED unenumerable chunk too (e.g. an [SFBrules] block inside
    [Module M]), not the real [M] it sits inside. *)
let opaque_entry_key (path : string) (id : Id.t) : string =
  let marked = opaque_entry_prefix ^ Id.to_string id in
  if path = "" then marked else path ^ "." ^ marked

let modtype_entry_marker = "0usage_cutoff_modtype_"
(** Reserved prefix, same uncollidable-with-any-real-identifier property
    as [opaque_entry_prefix] above (digit-leading -- see that constant's
    doc comment), applied by [mark_basename] to the BASENAME ONLY of
    every entry produced while recursing into an [SFBmodtype]'s own
    structure. Never applied to a qualified path's non-final segments, so
    [comp_iface]/[iface_subset_ok] (which compare the FULL path) see an
    ordinary-looking, still-unique-per-library key; [flatten_closure]'s
    shadow table (which strips to the basename via
    [basename_of_qualified_path]) sees an uncollidable one. *)
let mark_basename (marker : string) (path : string) : string =
  match String.rindex_opt path '.' with
  | Some i -> String.sub path 0 (i + 1) ^ marker ^ String.sub path (i + 1) (String.length path - i - 1)
  | None -> marker ^ path

(** Reserved key-construction scheme for the entry [iface_entries_of_sfb]
    adds for a [Module]'s or [Module Type]'s own LABEL (round 9 P1/mns1/
    mtns1: without an entry here, [flatten_closure]'s shadow table never
    saw the module/module-type NAME itself, only fields nested inside
    it). Round 10 shipped this as a PLAIN entry, [(qualify id,
    module_label_digest)] -- an unmarked key in the SAME basename space
    ordinary constants use. Round 11 then tried making the key encode the
    label's FULL nesting path (joined by ['#'], never truncated by
    [basename_of_qualified_path]), to fix two over-refusals the round-10
    review found (nd2/nd3: an unrelated TOP-LEVEL module colliding with a
    differently-nested one of the same innermost name; lc1/lc2: a
    module's label colliding with a same-named CONSTANT, though Rocq
    resolves module and term names through separate Nametab tables).

    **Round 11's full-path key was UNSOUND, found by Main (binary-
    equivalence-taiga#841 round 11 follow-up) and confirmed empirically
    before any code changed: nd5.** X declares a 2-level-nested `Module
    M. Module N. Definition f := 1.`. B does `Require Import X. Import
    M. Require Import A. Import N.` -- note the ORDER: `Import M.` runs
    BEFORE `Require Import A.`, which transitively re-exports W. When W
    later adds an UNRELATED TOP-LEVEL `Module N`, a bare `Import N.`
    issued AFTER `Require Import A` resolves to W's top-level N, not
    X's nested M.N, even though `Import M.` ran first and even though
    nd3's near-identical shape (X/A required TOGETHER, upfront, before
    any `Import`) resolves the OPPOSITE way. Confirmed directly: a FRESH
    compile of this exact B against the post-change W fails with "f was
    not found", proving the ambiguity is real and order-dependent, not a
    full-path-keys false negative -- Rocq's unqualified name resolution
    for a BARE `Import <name>` statement depends on REQUIRE/IMPORT ORDER,
    not merely on nesting depth, so a key that only ever compares full
    paths (ignoring that two DIFFERENT full paths can still compete for
    the SAME bare name depending on when each was brought into scope)
    misses this exactly the way basename-only keys were designed to
    catch. (nd5b, the same shape with `Definition b : N.f = 1 :=
    eq_refl.` -- a QUALIFIED reference, no bare `Import N.` statement at
    all -- does NOT diverge: `Import M.` already binds "N" to M's nested
    N as a local, transparent dot-accessible name, unaffected by any
    LATER `Require`; only a FRESH bare-name Nametab lookup, as `Import
    N.` performs, is order-sensitive this way.)

    **Fix (this round): back to the reviewer's own original shape --
    basename-only, namespaced away from constants, AND tagged by KIND
    (module vs. module type).** [mark_basename] (the SAME mechanism
    already used for [modtype_entry_marker] on module type fields) tags
    ONLY the label's own innermost segment, leaving any outer path intact
    in [comp_iface]'s own full-path key (same-library uniqueness,
    avoiding a kd1/kd2-style masking bug, unaffected by this).
    [flatten_closure]'s [basename_of_qualified_path] then extracts just
    the marked innermost segment -- IDENTICAL for X's nested `M.N`'s
    label and W's top-level `N`'s label (both [Module]s), so they DO
    collide, sound but imprecise exactly like the pre-round-11 bare-
    basename rule that already (correctly) refuses nd1/nd4/nd5/nd6/nd7/
    nd8/nd5t. nd2/nd3 (and now nd5/nd5b) go back to being OVER-refusals:
    Main's explicit ruling after nd5 ("leaves nd2/nd3 as over-refusals,
    which is sound") accepts this, since relaxing them without an order-
    aware, full Nametab-accurate model (replicating Rocq's own resolution
    precedence exactly) cannot be done soundly with a per-library digest
    table.

    **Two DIFFERENT markers, one per kind, not one shared marker
    (mvt3).** The reviewer's own follow-up (mvt3: X has `Module N`, W
    adds an unrelated `Module Type N`, B does `Import N.` -- a fresh
    compile succeeds regardless) found that Rocq resolves a module name
    and a module TYPE name through independent lookups: `Import`
    syntactically only ever accepts a module, never a module type, so a
    same-named module type anywhere is never even a candidate. A single
    shared marker for both kinds would make mvt3 wrongly collide (an
    over-refusal beyond what's sound, unlike nd2/nd3/nd5/nd5b, which are
    genuine, accepted basename-level imprecision); [module_label_marker]
    (for [SFBmodule]) and [modtype_label_marker] (for [SFBmodtype]'s own
    LABEL -- distinct from [modtype_entry_marker], which marks its
    FIELDS) keep the two kinds in their own, mutually disjoint G7
    sub-namespaces, so mvt3 reuses correctly while mns1 (module vs.
    module, same kind) and mtns1 (module type vs. module type, same
    kind) still refuse.

    Both markers still make labels uncollidable with any REAL constant's
    basename (['#'] cannot appear inside an identifier the parser
    accepts, confirmed empirically: `Definition a#b := 0.` is a syntax
    error, parsed as two tokens) -- so lc1/lc2 stay fixed, the one part
    of round 11's fix this round keeps. Neither marker is excluded by
    [is_marked_basename] (which checks only a digit-leading first
    character): a label must still PARTICIPATE in ordinary G7 cross-
    library comparison, unlike an [opaque_entry_prefix]/
    [modtype_entry_marker] entry, which is deliberately excluded
    entirely.

    **What this does NOT fix, recorded as a known limitation, not
    built.** nd2/nd3/nd5/nd5b stay refused; nd6 ([Export] instead of a
    later [Import]), nd7 (the colliding module nested inside an
    [Export]ed [Module K]), and nd8 (a qualified [Import M.N] binding to
    an UNRELATED library's [Z.M.N] after [Export Z], since qualids
    resolve by path SUFFIX to ANY depth) all confirm the SAME shape of
    gap generalizes arbitrarily: Rocq's actual name resolution is a
    suffix search over every name currently in scope, order- and
    export-sensitive, which no per-library digest table keyed by a
    bounded amount of path context can fully replicate. The precise
    alternative -- recording, at the VERNAC layer (which alone sees the
    resolved [Libnames.qualid] a `Require`/`Import`/`Module ... : T`
    statement actually bound), exactly which qualified name each
    unqualified reference in a file resolved to, and checking THAT
    specific binding instead of a coarse basename -- is the next step for
    these remaining over-refusals, and is NOT built this round. *)
(* module_label_marker/modtype_label_marker are now defined earlier,
   just after is_marked_basename, since closure_subset_ok needs them too. *)

(** The digest value paired with every module/module-type label entry.
    Not load-bearing for soundness: [closure_subset_ok]/[iface_subset_ok]
    key on the full [(dp, id)] pair, and a module's/module-type's own
    internal content is independently covered by its recursively-produced
    field entries. A single constant suffices. *)
let module_label_digest = Csha256.digest "0usage_cutoff_module_label"

let rec iface_entries_of_struct (path : string) (sb : structure_body)
    : (string * Digest.t) list =
  List.concat_map (fun (id, sfb) -> iface_entries_of_sfb path (id, sfb)) sb

and entries_of_signature (path : string) (id : Id.t) (msig : module_signature)
    : (string * Digest.t) list =
  let sub_path = if path = "" then Id.to_string id else path ^ "." ^ Id.to_string id in
  match msig with
  | NoFunctor sb' -> iface_entries_of_struct sub_path sb'
  | MoreFunctor _ ->
    [(opaque_entry_key path id, Csha256.digest (Marshal.to_string msig []))]

and iface_entries_of_sfb (path : string) (id, sfb) : (string * Digest.t) list =
  let qualify id = if path = "" then Id.to_string id else path ^ "." ^ Id.to_string id in
  match sfb with
  | SFBconst cb -> [(qualify id, iface_digest_of_const cb)]
  | SFBmind mib ->
    let d = iface_digest_of_mind mib in
    let names = ref [] in
    Array.iter (fun mip ->
        names := mip.mind_typename :: !names;
        Array.iter (fun c -> names := c :: !names) mip.mind_consnames)
      mib.mind_packets;
    List.map (fun n -> (qualify n, d)) !names
  | SFBrules r ->
    [(opaque_entry_key path id, Csha256.digest (Marshal.to_string r []))]
  | SFBmodule mb ->
    (mark_basename module_label_marker (qualify id), module_label_digest) :: entries_of_signature path id (mod_type mb)
  | SFBmodtype mtb ->
    (mark_basename modtype_label_marker (qualify id), module_label_digest) ::
    List.map (fun (k, d) -> (mark_basename modtype_entry_marker k, d))
      (entries_of_signature path id (mod_type mtb))

let iface_table_of_struct (sb : structure_body) : iface_table option =
  Some (Array.of_list (iface_entries_of_struct "" sb))

let export ~output_native_objects ~objects_digest ~vernac_iface ~extra_closure_names senv dir =
  let () = check_current_library dir senv in
  let mp = senv.modpath in
  let str = NoFunctor (List.rev senv.revstruct) in
  let mb = Mod_declarations.make_module_body str senv.modresolver senv.local_retroknowledge in
  let ast, symbols =
    if output_native_objects then
      Nativelibrary.dump_library mp senv.env str
    else [], Nativevalues.empty_symbols
  in
  let permanent_flags = {
    rewrite_rules_allowed = Environ.rewrite_rules_allowed senv.env;
  } in
  (* Disqualify a library whose module carries non-empty retroknowledge
     ([Register]/[Primitive]) from the relaxed path entirely: retroknowledge
     lives inside [comp_mod] (set via [make_module_body] above), invisible
     to both [comp_iface] (walks only [SFBconst]/[SFBmind]) and the vernac
     objects digest (kernel has no visibility into [Declaremods]). A
     retroknowledge-only change could otherwise pass both checks while
     silently changing VM/native-compute semantics (OracleRedTeamV2,
     binary-equivalence-taiga#841). Falling back to [None] here forces
     [dep_ok]'s [digest_match]-only path for such a library, the same
     "fall back to stock behavior when this mechanism can't represent
     something" pattern already used for nested modules/module
     types/rewrite-rules blocks below. In practice this only ever disarms
     Corelib (the only thing that calls [Register]/[Primitive]), which is
     toolchain-pinned and outside any agent's edit loop. #861's `Dvo_iface`
     (the whole-library identity, commit 1) digests [comp_mod] wholesale
     and so already covers retroknowledge on its own path (confirmed by
     Plan861InterfaceReuse against kernel/modops.ml:169-170,195-197 and
     checker/{safe_checking.ml:24,mod_checking.ml:317}) -- this
     disqualification is needed only for THIS design's second, finer
     per-declaration fallback layer, which Dvo_iface does not gate. *)
  let has_retroknowledge = not (List.is_empty senv.local_retroknowledge) in
  let comp_iface = if has_retroknowledge then None else match str with
    | NoFunctor sb -> iface_table_of_struct sb
    | MoreFunctor _ -> None
  in
  (* binary-equivalence-taiga#841 round 7 (ab1): [extra_closure_names] is
     the vernac layer's own contribution of (Id.t, Digest.t) entries for
     names this library exports that the kernel's OWN structure_body walk
     can never see -- currently just abbreviations
     ([Declaremods.G1Partition.abbrev_iface_entries], sourced from
     [Abbreviation.cutoff_abbrev_entry]). Folded directly into the SAME
     [comp_iface] table an ordinary [SFBconst] would land in: that table
     feeds BOTH [iface_subset_ok] (this library's own content changing
     forces refusal) and [flatten_closure] (a LATER library's addition
     colliding with this name is refused too) for free, with no separate
     mechanism. Dropped when [comp_iface] is [None] (has_retroknowledge):
     consistent with every other case this mechanism cannot represent,
     already falling back to the sound, conservative whole-library
     [digest_match] path. *)
  let comp_iface = Option.map (fun tbl -> Array.append tbl extra_closure_names) comp_iface in
  (* G7 round 5: this library's (B's) own full transitive closure,
     flattened once here and attached to EVERY kept dependency entry
     below (the SAME value for each -- [dep_ok] treats it as a single
     per-[check_required]-call constant, not per-entry data; storing it
     redundantly per entry avoids a second signature on [check_required]/
     [check_required_strict] for a single extra argument). See
     [flatten_closure]'s doc comment. *)
  (* binary-equivalence-taiga#841 round 14 (ik7/ik8, Main/reviewer): a
     library can Include a Module Type it declares ITSELF, and ModAny
     tries a module lookup first regardless of declaration order/locality
     -- a module of the same bare name appearing ANYWHERE in scope
     (including an EXTERNAL one reached only transitively) can still win
     over this library's OWN, textually-local Module Type. Folding this
     library's OWN [comp_iface] (dp = [dir], the library's own path) into
     [own_closure_list] gives its own module-type labels the SAME
     cross-kind shadow coverage [closure_subset_ok] already gives an
     external library's -- a brand-new external MODULE of the same
     basename is now checked against them too, covering nested self
     module types (ik8) for free, since [comp_iface] already recurses to
     any depth. The placeholder digest is never compared against
     anything meaningful ([Some comp_iface] is the branch flatten_closure
     reads; [None]'s [none_entries] never sees this entry). *)
  let self_modtype_iface =
    Option.map (fun tbl ->
        Array.of_list
          (List.filter (fun (k, _) ->
               Option.has_some (strip_prefix modtype_label_marker (Id.to_string (basename_of_qualified_path k))))
              (Array.to_list tbl)))
      comp_iface
  in
  let own_closure_list =
    (dir, Dvo_or_vi (Digest.string "self"), self_modtype_iface) ::
    (DirPath.Map.bindings senv.required
     |> List.map (fun (dp, { req_digest; req_iface; _ }) -> (dp, req_digest, req_iface)))
  in
  let comp_closure_names, comp_closure_none_digest = flatten_closure own_closure_list in
  (* v2's D1 (full transitive closure, [comp_transitive_deps]/
     [md_transitive_deps] as a SEPARATE field) lands as part of commit 1 on
     `sami/861-loc-free-identity`; this slice keeps [comp_deps] root-only,
     byte-for-byte the same filtering stock/v1 already use, so
     [compute_modes]/[check_closure_conflicts] (which read this exact
     field) are untouched and this slice is independently buildable and
     testable before commit 1 exists. Rebasing onto commit 1 swaps this
     block for the full-closure field without touching [compute_modes] at
     all (binary-equivalence-taiga#841 "D1"). *)
  let filter_dep (dp, { req_root; req_digest; req_iface; req_objects_digest;
                         req_univs_digest; req_vernac_iface }) =
    if req_root then Some (dp, req_digest, req_iface, req_objects_digest,
                            req_univs_digest, req_vernac_iface,
                            comp_closure_names, comp_closure_none_digest)
    else None
  in
  let comp_deps = List.map_filter filter_dep (DirPath.Map.bindings senv.required) in
  (* binary-equivalence-taiga#841 Review841 G2: digest of this library's OWN
     global universe constraints/sort qualities, computed here (not handed
     in like [objects_digest]) since the kernel already has both values.
     SHA-256 (Lean attack-battery D3), not MD5: see [iface_digest_of_const]'s
     doc comment. *)
  let comp_univs_digest =
    Csha256.digest (Marshal.to_string (senv.univ, senv.qualities) [])
  in
  let lib = {
    comp_name = dir;
    comp_mod = mb;
    comp_univs = senv.univ;
    comp_sorts = senv.qualities;
    comp_deps = Array.of_list comp_deps;
    comp_flags = permanent_flags;
    comp_iface;
    comp_objects_digest = objects_digest;
    comp_univs_digest;
    comp_vernac_iface = vernac_iface;
    comp_closure_names;
    comp_closure_none_digest;
  } in
  let vmlib = Vmlibrary.export @@ Environ.vm_library senv.env in
  mp, lib, vmlib, (ast, symbols)

let import_gen ~check_required lib vmtab vodigest senv =
  let senv = check_flags_for_library lib senv in
  let required = check_required senv.required lib.comp_deps in
  if DirPath.equal (ModPath.dp senv.modpath) lib.comp_name then
    CErrors.user_err
      Pp.(strbrk "Cannot load a library with the same name as the current one ("
          ++ DirPath.print lib.comp_name ++ str").");
  let mp = MPfile lib.comp_name in
  let mb = lib.comp_mod in
  let univs = lib.comp_univs in
  let qualities = lib.comp_sorts in
  let check_quality q =
    Sorts.QVar.is_global q &&
    not (QGraph.is_declared (Sorts.Quality.QVar q) (Environ.qualities senv.env))
  in
  let () = assert (Sorts.QVar.Set.for_all check_quality (fst qualities)) in
  let env = Environ.push_qualities ~rigid:true qualities senv.env in
  let env = Environ.push_context_set ~strict:true univs env in
  let env = Environ.link_vm_library vmtab env in
  let env =
    let linkinfo = Nativecode.link_info_of_dirpath lib.comp_name in
    Modops.add_linked_module mp mb linkinfo env
  in
  let sections =
    Option.map (Section.map_custom (fun custom ->
        {custom with rev_reimport = (lib,vmtab,vodigest) :: custom.rev_reimport}))
      senv.sections
  in
  let required =
    if DirPath.Map.mem lib.comp_name required then
      (* should probably be an error, we are requiring the same library twice *)
      required
    else DirPath.Map.add lib.comp_name
        { req_root = true; req_digest = vodigest; req_iface = lib.comp_iface;
          req_objects_digest = lib.comp_objects_digest;
          req_univs_digest = lib.comp_univs_digest;
          req_vernac_iface = lib.comp_vernac_iface } required
  in
  mp,
  { senv with
    env;
    (* Do NOT store the name quotient from the dependencies in the set of
       constraints that will be marshalled on disk. *)
    paramresolver = ParamResolver.add_delta_resolver mp (mod_delta mb) senv.paramresolver;
    required;
    loads = (mp,mb)::senv.loads;
    sections;
  }

let import lib vmtab vodigest senv =
  import_gen ~check_required lib vmtab vodigest senv

(** The ONLY entry point [checker/safe_checking.ml] may call: every
    dependency is checked by whole-library digest equality alone, with the
    relaxed fallback not merely untaken but absent from this function's own
    body (see [check_required_strict]'s doc comment). *)
let import_strict lib vmtab vodigest senv =
  import_gen ~check_required:check_required_strict lib vmtab vodigest senv

(** {6 Interactive sections} *)

let open_section senv =
  let custom = {
    rev_env = senv.env;
    rev_univ = senv.univ;
    rev_qualities = senv.qualities;
    rev_objlabels = senv.objlabels;
    rev_reimport = [];
    rev_revstruct = senv.revstruct;
    rev_paramresolver = senv.paramresolver;
  } in
  let sections = Section.open_section ~custom senv.sections in
  { senv with sections=Some sections }

let close_section senv =
  let open Section in
  let sections0 = get_section senv.sections in
  let env0 = senv.env in
  (* First phase: revert the declarations added in the section *)
  let sections, entries, cstrs, revert = Section.close_section sections0 in
  (* Don't revert the delayed constraints (future_cst). If some delayed constraints
     were forced inside the section, they have been turned into global monomorphic
     that are going to be replayed. Those that are not forced are not readded
     by {!add_constant_aux}. *)
  let { rev_env = env; rev_univ = univ; rev_qualities = qualities; rev_objlabels = objlabels;
        rev_reimport; rev_revstruct = revstruct; rev_paramresolver = paramresolver } = revert in
  let env = if Environ.rewrite_rules_allowed env0 then Environ.allow_rewrite_rules env else env in
  let senv = { senv with env; revstruct; sections; univ; qualities; objlabels; paramresolver } in
  (* Second phase: replay Requires *)
  let senv = List.fold_left (fun senv (lib,vmtab,vodigest) -> snd (import lib vmtab vodigest senv))
      senv (List.rev rev_reimport)
  in
  (* Third phase: replay the discharged section contents *)
  let senv = push_context_set ~strict:true cstrs senv in
  let fold entry senv =
    match entry with
  | SecDefinition kn ->
    let cb = Environ.lookup_constant kn env0 in
    let info = Section.segment_of_constant kn sections0 in
    let cb = Discharge.cook_constant senv.env info cb in
    let cb = compile_bytecode senv.env cb in
    (* Delayed constants are already in the global environment *)
    add_constant_aux senv (kn, cb)
  | SecInductive ind ->
    let mib = Environ.lookup_mind ind env0 in
    let info = Section.segment_of_inductive ind sections0 in
    let mib = Discharge.cook_inductive info mib in
    add_checked_mind ind mib senv
  in
  List.fold_right fold entries senv

let flatten_env senv =
  let label = function MPdot (_,l) -> l | _ -> assert false in
  let rec close senv =
    match senv.modvariant with
    | STRUCT _ -> close (snd (end_module (label senv.modpath) None senv))
    | SIG (params,env) -> close (snd (end_module (label senv.modpath) None {senv with modvariant = STRUCT (params,env)}))
    | LIBRARY | NONE -> senv in
  let senv = close senv in
  (senv.modpath, senv.revstruct)

(** {6 Safe typing } *)

type judgment = {
  jdg_env : safe_environment;
  jdg_val : constr;
  jdg_type : types;
}

let typing senv c =
  let j = Typeops.infer (env_of_senv senv) c in
  { jdg_env = senv;
    jdg_val = j.Environ.uj_val;
    jdg_type = j.Environ.uj_type;
  }

(** {6 Retroknowledge / native compiler } *)

let register_inline kn senv =
  let open Environ in
  if not (evaluable_constant kn senv.env) then
    CErrors.user_err Pp.(str "Register inline: an evaluable constant is expected");
  let env = senv.env in
  let cb = lookup_constant kn env in
  let cb = {cb with const_inline_code = true} in
  let env = add_constant kn cb env in { senv with env}

let check_register_ind (type t) ind (r : t CPrimitives.prim_ind) env =
  let (mb,ob as spec) = Inductive.lookup_mind_specif env ind in
  let ind = match mb.mind_universes with
    | Polymorphic _ -> CErrors.user_err Pp.(str "A universe monomorphic inductive type is expected.")
    | Monomorphic -> Constr.UnsafeMonomorphic.mkInd ind
  in
  let check_if b msg =
    if not b then
      CErrors.user_err msg in
  check_if (Int.equal (Array.length mb.mind_packets) 1) Pp.(str "A non mutual inductive is expected.");
  check_if (not @@ Inductive.is_private spec) Pp.(str "A non-private inductive type is expected");
  let check_nparams n =
    check_if (Int.equal mb.mind_nparams n) Pp.(str "An inductive type with " ++ int n ++ str " parameters is expected")
  in
  let check_nconstr n =
    check_if (Int.equal (Array.length ob.mind_consnames) n)
      Pp.(str "an inductive type with " ++ int n ++ str " constructors is expected")
  in
  let check_name pos s =
    check_if (Id.equal ob.mind_consnames.(pos) (Id.of_string s))
      Pp.(str"the " ++ int (pos + 1) ++ str
       "th constructor does not have the expected name: " ++ str s) in
  let check_type pos t =
    check_if (Constr.equal t ob.mind_user_lc.(pos))
      Pp.(str"the " ++ int (pos + 1) ++ str
       "th constructor does not have the expected type") in
  let check_type_cte pos = check_type pos ind in
  match r with
  | CPrimitives.PIT_bool ->
    check_nparams 0;
    check_nconstr 2;
    check_name 0 "true";
    check_type_cte 0;
    check_name 1 "false";
    check_type_cte 1
  | CPrimitives.PIT_carry ->
    check_nparams 1;
    check_nconstr 2;
    let test_type pos =
      let c = ob.mind_user_lc.(pos) in
      let s = Pp.(str"the " ++ int (pos + 1) ++ str
              "th constructor does not have the expected type") in
      check_if (Constr.isProd c) s;
      let (_,d,cd) = Constr.destProd c in
      check_if (Constr.is_Type d) s;
      check_if
        (Constr.equal
                (mkProd (Context.anonR,mkRel 1, mkApp (ind,[|mkRel 2|])))
                cd)
        s in
    check_name 0 "C0";
    test_type 0;
    check_name 1 "C1";
    test_type 1;
  | CPrimitives.PIT_pair ->
    check_nparams 2;
    check_nconstr 1;
    check_name 0 "pair";
    let c = ob.mind_user_lc.(0) in
    let s =  Pp.str "the constructor does not have the expected type" in
    begin match Term.decompose_prod c with
      | ([_,b;_,a;_,_B;_,_A], codom) ->
        check_if (is_Type _A) s;
        check_if (is_Type _B) s;
        check_if (Constr.equal a (mkRel 2)) s;
        check_if (Constr.equal b (mkRel 2)) s;
        check_if (Constr.equal codom (mkApp (ind,[|mkRel 4; mkRel 3|]))) s
      | _ -> check_if false s
    end
  | CPrimitives.PIT_cmp ->
    check_nparams 0;
    check_nconstr 3;
    check_name 0 "Eq";
    check_type_cte 0;
    check_name 1 "Lt";
    check_type_cte 1;
    check_name 2 "Gt";
    check_type_cte 2
  | CPrimitives.PIT_f_cmp ->
    check_nconstr 4;
    check_name 0 "FEq";
    check_type_cte 0;
    check_name 1 "FLt";
    check_type_cte 1;
    check_name 2 "FGt";
    check_type_cte 2;
    check_name 3 "FNotComparable";
    check_type_cte 3
  | CPrimitives.PIT_f_class ->
    check_nconstr 9;
    check_name 0 "PNormal";
    check_type_cte 0;
    check_name 1 "NNormal";
    check_type_cte 1;
    check_name 2 "PSubn";
    check_type_cte 2;
    check_name 3 "NSubn";
    check_type_cte 3;
    check_name 4 "PZero";
    check_type_cte 4;
    check_name 5 "NZero";
    check_type_cte 5;
    check_name 6 "PInf";
    check_type_cte 6;
    check_name 7 "NInf";
    check_type_cte 7;
    check_name 8 "NaN";
    check_type_cte 8

let register_inductive ind prim senv =
  check_register_ind ind prim senv.env;
  let action = Retroknowledge.Register_ind(prim,ind) in
  add_retroknowledge action senv

(* NB: The next old comment probably refers to [propagate_loads] above.
   When a Require is done inside a module, we'll redo this require
   at the upper level after the module is ended, and so on.
   This is probably not a big deal anyway, since these Require's
   inside modules should be pretty rare. Maybe someday we could
   brutally forbid this tricky "feature"... *)

(* we have an inefficiency: Since loaded files are added to the
environment every time a module is closed, their components are
calculated many times. This could be avoided in several ways:

1 - for each file create a dummy environment containing only this
file's components, merge this environment with the global
environment, and store for the future (instead of just its type)

2 - create "persistent modules" environment table in Environ add put
loaded by side-effect once and for all (like it is done in OCaml).
Would this be correct with respect to undo's and stuff ?
*)

let set_oracle ts e =
  { e with env = Environ.set_oracle e.env ts }

let set_strategy k l e = { e with env =
   (Environ.set_oracle e.env
      (Conv_oracle.set_strategy (Environ.oracle e.env) k l)) }
