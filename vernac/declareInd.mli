(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Registering a mutual inductive definition together with its
   associated schemes *)

type one_inductive_impls =
  Impargs.manual_implicits (* for inds *) *
  Impargs.manual_implicits list (* for constrs *)

type default_dep_elim = DefaultElim | PropButDepElim

type indlocs = (Loc.t option * Loc.t option list) list
(** Inductive type and constructor locs, for .glob and src loc info *)

type declare_schemes = None | Default

val schemes_attr : declare_schemes Attributes.attribute

val declare_mutual_inductive_with_eliminations
  : ?typing_flags:Declarations.typing_flags
  -> ?indlocs:indlocs
  -> ?default_dep_elim:default_dep_elim list
  -> ?schemes:declare_schemes
  -> ?all_depth:int
  -> Entries.mutual_inductive_entry (* Inductive types declaration *)
  -> UState.named_universes_entry (* Global universes, including the template default instance *)
  -> one_inductive_impls list (* Implicit arguments *)
  -> Names.MutInd.t

(** Create the All predicate with its theorem all_forall. *)
val do_scheme_all : Libnames.qualid Constrexpr.or_by_notation -> Names.Id.t list option -> unit


(** {6 For legacy support, do not use}  *)
module Internal :
sig

type inductive_obj
val objInductive : (Names.Id.t * inductive_obj) Libobject.Dyn.tag
val objPrimProj : (Names.Projection.Repr.t * Names.Constant.t) Libobject.Dyn.tag
(** binary-equivalence-taiga#841 Review841 G1: exposed only so
    [Declaremods.G1Partition] can structurally verify an atomic object
    before excluding it by tag name -- see the implementation's doc
    comment on [Internal.objPrimProj] for why a bare tag-string match is
    not enough. *)

end

val declare_primitive_projection :
  Names.Projection.Repr.t -> Names.Constant.t -> unit
