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

type t = {
  assumptions : string list option;
  (** The assumption closure (axioms and other [ContextObject]s, as sorted
      canonical keys) every constant and inductive of the library transitively
      relies on, traversing opaque proof bodies as [Print Assumptions] does.
      [None] when it could not be computed. *)
  opacity_queries : (string * bool) list;
  (** Each foreign constant (canonical kernel name) a non-opaque
      [Strategy]/[Transparent] command named, with the opacity it saw, sorted. *)
}

val compute : access:Global.indirect_accessor -> self:DirPath.t -> t
(** The facts for the library [self], computed from the current environment
    (its constants and inductives, and the opaque bodies [access] reaches).
    Call it while the library being saved is still loaded. *)
