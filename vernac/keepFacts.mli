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

(** The keep rule's facts about a saved library that a [.vo] file's segments
    cannot carry on their own (design D18, dispatch://INFRA-361): its
    assumption closure, and the foreign opacities its strategy commands saw.
    [Library] computes them while the library is saved and stores them in a
    [keepfacts] segment the label does not cover. *)

type query = {
  constant : string;  (** its user name, as [LibkeyObjects.axiom_report] lists it *)
  library : string option;  (** the library holding it; [None] for a functor parameter's *)
  opaque : bool;  (** whether it was an opaque proof when the command ran *)
}

type t = {
  assumptions : (string * string list) list option;
  (** The assumption closure of each constant and inductive the library
      declares (by user name; sorted; empty closures left out): its axioms
      and other [ContextObject]s as sorted canonical keys, plus theory flags,
      traversing opaque proof bodies as [Print Assumptions] does. [None] when
      it could not be computed. *)
  opacity_queries : query list;
  (** Each foreign constant a command told apart as an axiom ([Undef None]) or
      an opaque proof (a non-opaque [Strategy]/[Transparent] command, an
      extraction: [OpacityLog]), or whose opaque proof body an extraction
      read (always [opaque = true]), with its library and the opacity it saw,
      sorted by name; recorded both ways, [opaque = true]. No other body form
      is recorded. *)
}

val compute :
  access:Global.indirect_accessor ->
  stored:(DirPath.t -> (string * string list) list option) -> self:DirPath.t -> t
(** The facts for the library [self], computed from the current environment
    (its constants and inductives, and the opaque bodies [access] reaches).
    Call it while the library being saved is still loaded. [stored dp] is the
    [assumptions] field of the keepfacts segment of the loaded library [dp]
    (read with its other segments), or [None]: the closure of a constant of
    such a library is taken from there rather than by walking it. That gives
    the closure [Print Assumptions] gives when no library it reaches was
    recompiled since [dp] was. After a dependency was rebuilt to an equal label
    under a kept [dp] (a keep round), it gives a superset: [dp]'s record still
    lists what the dependency's old build used, and the keep rule keeps [dp]
    only when no closure of its in-tree dependencies grew, so the record still
    contains every current closure (the comment of [fast_closures] gives the
    induction). ROCQ_KEEPFACTS_FULL_WALK=1 walks every body instead (the
    current closure exactly, the reference this is checked against), and
    ROCQ_KEEPFACTS_DEBUG=1 says on standard error how each library's closures
    were computed. *)
