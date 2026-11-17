(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The axioms and the relaxed typing flags that a constant rests on, for
    [rocqchk -compare]. *)

(** {6 The kinds of the relaxed typing flags}

    As the config and the verdict name them. *)

val type_in_type : string
val unsafe_fixpoint : string
val unchecked_eliminations : string
val assumed_positive : string
val uip : string
val indices_not_mattering : string

(** {6 The closure} *)

type closure_state

val closure_state :
  Environ.env -> (Opaqueproof.opaque -> Opaqueproof.opaque_proofterm) -> closure_state
(** A state the walk's caches live in; share one across the constants of a
    run. *)

val axioms_and_flags :
  closure_state -> Names.Constant.t ->
  (string * Names.GlobRef.t) list * (string * string * Names.GlobRef.t) list
(** The axioms the constant's proof reaches, each with the name it prints,
    sorted by that name, and the relaxed typing flags [(kind, printed
    object, object)] it rests on, sorted by kind and printed name.

    The axioms are the constants without a body, the primitives and the
    symbols among the constant and what its body and type reach, and the
    objects that neither the environment nor a module implementation
    resolves. A term uses its declaration in the environment when that
    declaration has a body; a declaration that a module signature leaves
    without a body uses the body that the module's implementation gives it,
    and the terms of that body are resolved in the implementation too. This
    keeps an implementation proof's typing conditions from being replaced by
    an independent signature proof.
    An opaque body that cannot be read counts as an axiom, with a warning.
    Literal and array terms also reach their registered primitive type. The
    flags are the relaxed typing conditions of what is reached:
    [type-in-type], [unsafe-fixpoint], [unchecked-eliminations],
    [assumed-positive], [uip] and [indices-not-mattering].

    An axiom or a flag's object is the object itself: two objects that print
    the same name are two entries ([R.P.Q.g] can be the constant [g] of the
    library [R.P.Q] or the constant [g] of a module [Q] of the library
    [R.P]). A flag of an inductive block names its first inductive.

    @raise CErrors.UserError when the closure reaches an axiom or a flag's
    object whose printed name is not made of identifiers, or an inductive
    block with a type name that is not an identifier ([CheckNames]). *)
