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
open Constr
open Printer

(** Collects all the objects on which terms directly rely, bypassing kernel
    opacity, together with the recursive dependence DAG of objects.

    WARNING: some terms may not make sense in the environment, because they are
    sealed inside opaque modules. Do not try to do anything fancy with those
    terms apart from printing them, otherwise demons may fly out of your nose.

    NOTE: this function is used in the plugins paramcoq and metarocq.
*)
val traverse :
  Global.indirect_accessor -> GlobRef.t list ->
    (GlobRef.Set_env.t * GlobRef.Set_env.t option GlobRef.Map_env.t *
     (GlobRef.t * Constr.rel_context * types) list GlobRef.Map_env.t)

(** Collects all the assumptions (optionally including opaque definitions)
   on which terms rely (together with their type). The above warning of
   {!traverse} also applies. *)
val assumptions :
  ?add_opaque:bool -> ?add_transparent:bool -> Global.indirect_accessor ->
  TransparentState.t -> GlobRef.t list ->
  theory_assumptions * types ContextObjectMap.t

(** One walk from all of [grs], as {!traverse}'s with one graph for them all,
    that reads and records no reuse entry (it is not a query of the reuse that
    {!assumptions} queries share) and does not enter an object for which
    [stop] holds: such an object, and for an inductive every member of its
    block, is in the graph with no edges ([Some] of the empty set). The graph
    maps each object the walk reaches to its value in {!traverse}'s graph: the
    set of its direct references, or [None] for an object walked without a
    body, whose direct references are those of its type
    ({!type_references}). The boolean says whether the walk met a match on an
    empty type over an axiom, which marks that axiom reached without walking
    its type, so that what such a walk reaches depends on the order it visits
    objects in (vernac/keepFacts.ml then computes no closure from the graph).
    Used by [KeepFacts] for the assumption closure of each declaration of a
    library at once. *)
val reach :
  stop:(GlobRef.t -> bool) -> Global.indirect_accessor -> GlobRef.t list ->
  GlobRef.Set_env.t option GlobRef.Map_env.t * bool

(** What {!assumptions}, with neither [add_opaque] nor [add_transparent],
    adds for the object [obj] alone, given its value in the graph of a walk
    that reached it ({!reach}): {!assumptions} of [grs] is the union of this
    over every object its walk reaches. [access] is the accessor that walk
    used; this reads no body through it, only whether the kernel typed an
    opaque proof it already read ([-skip-qed-typecheck]). The empty-match
    contexts an [Axiom] carries for printing are left empty. *)
val object_assumptions :
  Global.indirect_accessor -> GlobRef.t -> GlobRef.Set_env.t option ->
  theory_assumptions * types ContextObjectMap.t

(** The references a walk collects from the type of a constant without a
    body: the direct references of an object that {!reach}'s graph maps to
    [None]. *)
val type_references : Constant.t -> GlobRef.Set_env.t

(** While a walk ({!assumptions}, {!reach}) reads an opaque proof's body
    through the accessor it was given, the constant whose body it reads (as
    the walk reached it, by its user name); [None] at any other time. Every
    accessor call a walk makes is such a read, so an accessor that wraps the
    one the walk is given can name each table read ([KeepFacts]). *)
val reading_constant : unit -> Constant.t option

(** What a walk's reuse of earlier walks reads about the libraries loaded:
    the generation of their opaque tables
    ([Library.opaque_tables_generation]), which keys the entries a query
    leaves for the next one, and their content digests
    ([Library.content_digests]), which key what the processes of one build
    share. [Library] registers it, rather than this module calling it: the
    keep rule puts [Library] above this module ([Library] -> [KeepFacts] ->
    here), so a call the other way is a module cycle. Unregistered, no query
    reuses another's entries and no object is shared. *)
type library_facts = {
  opaque_tables_generation : unit -> int;
  content_digests : unit -> (DirPath.t -> Digest.t option);
}

val set_library_facts : library_facts -> unit
