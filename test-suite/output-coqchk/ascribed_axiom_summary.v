(* An ascription over a module expression, [Module M : T := E], puts T in the
   environment: a field T declares as a parameter has no body there even where
   E defines it. The summary read that as an axiom and named it, while
   Print Assumptions resolves the field through the implementation and reads a
   proof that uses it closed (dispatch://BET-245). No shape below whose
   expression defines the field is listed here, each whose expression assumes
   it is, under the name Print Assumptions prints for the proof beside it,
   and the three it keeps that no proof's Print Assumptions names say so
   where they are declared: OfType.Asc.p, and Assumes.p and
   AssumesInside.Asc.p, which the environment holds in their own right and
   the fold over it always listed, whether a proof reaches them or not.
   misc/rocqchk_ascribed_axiom_summary.sh reads the two accounts against each
   other over this same file.

   The first half is inside a seal, where the summary holds the names of an
   implementation the environment does not; the second half is in the open,
   where the environment holds the ascribed module itself. *)

Module Type U. Parameter p : nat. End U.
Module Type T. Parameter q : nat. End T.

(* The expression defines p, so nothing here is assumed. *)
Module Defines. Definition p := 0. End Defines.
Module OverDefinition : T.
  Module Asc : U := Defines.
  Definition q := Asc.p.
End OverDefinition.
Definition over_definition := OverDefinition.q.

(* The expression assumes p. The axiom is named under the path the proof
   wrote, which is the name Print Assumptions prints for it too. Assumes.p is
   listed in its own right: the environment holds it. *)
Module Assumes. Axiom p : nat. End Assumes.
Module OverAxiom : T.
  Module Asc : U := Assumes.
  Definition q := Asc.p.
End OverAxiom.
Definition over_axiom := OverAxiom.q.

(* An alias of the defining module, and a module sealed in its own right:
   the walk follows the one to the other, and reads the implementation of
   whatever it ends at. *)
Module Mid := Defines.
Module Sealed : U. Definition p := 0. End Sealed.
Module OverChain : T.
  Module ViaAlias : U := Mid.
  Module ViaSeal : U := Sealed.
  Definition q := ViaAlias.p + ViaSeal.p.
End OverChain.
Definition over_chain := OverChain.q.

(* A field of a module the ascribed module's expression defines, one level
   below the ascription. *)
Module Type WithSub. Declare Module Sub : U. End WithSub.
Module DefinesSub. Module Sub. Definition p := 0. End Sub. End DefinesSub.
Module OverSubmodule : T.
  Module Asc : WithSub := DefinesSub.
  Definition q := Asc.Sub.p.
End OverSubmodule.
Definition over_submodule := OverSubmodule.q.

(* An [Include] inside a sealed structure: the structure defines the field,
   whatever the interface over it says. *)
Module OverInclude : T.
  Module M : U.
    Include Defines.
  End M.
  Definition q := M.p.
End OverInclude.
Definition over_include := OverInclude.q.

(* A definition the expression gives that rests on a global axiom: the field
   is not named, and the axiom it rests on still is, which is the name Print
   Assumptions prints. *)
Axiom global_ax : nat.
Module DefinesOverAxiom. Definition p := global_ax. End DefinesOverAxiom.
Module OverGlobalAxiom : T.
  Module Asc : U := DefinesOverAxiom.
  Definition q := Asc.p.
End OverGlobalAxiom.
Definition over_global_axiom := OverGlobalAxiom.q.

(* A module the sealed implementation declares itself, which no expression
   defines: its axiom is still named where it is declared. *)
Module Nested : T.
  Module Plain.
    Axiom inner_ax : nat.
  End Plain.
  Definition q := Plain.inner_ax.
End Nested.
Definition nested := Nested.q.

(* In the open, with no seal over it: the same two answers, from the fold over
   the environment rather than from what the checker recorded of a seal. *)
Module Open : U := Defines.
Definition open_definition := Open.p.

Module OpenAssumed : U := Assumes.
Definition open_axiom := OpenAssumed.p.

(* A module the environment holds as a parameter of its own: nothing defines
   it, so it stays named. *)
Declare Module Declared : U.
Definition declared := Declared.p.

(* A definition the expression gives with [Qed]: opaque, and a definition
   all the same. *)
Module Type UProp. Parameter p : True. End UProp.
Module DefinesOpaque. Lemma p : True. Proof. exact I. Qed. End DefinesOpaque.
Module OpenOpaque : UProp := DefinesOpaque.
Definition open_opaque := OpenOpaque.p.

(* A module type can carry [Module M : U := E] of its own, and it says
   nothing about what an implementation of that type binds. Both shapes below
   stay named: the first has no implementation at all, and the second has one
   this walk cannot read, whose own module assumes p. Print Assumptions names
   the second too. *)
Module Type WithExpression. Module Asc : U := Defines. End WithExpression.

Declare Module OfType : WithExpression.
Definition of_type := OfType.Asc.p.

Module Functor (X : U) : WithExpression.
  Module Assumed. Axiom p : nat. End Assumed.
  Module Asc : U := Assumed.
End Functor.
Module Applied := Functor Defines.
Definition applied := Applied.Asc.p.

(* A module ascribed to a type that carries an expression of its own, inside
   a seal, over an implementation that assumes the field. The type says
   [Defines], the implementation says [Assumes], and the implementation is
   what counts: both accounts name the field. *)
Module Type WithExpressionR.
  Module Asc : U := Defines.
  Definition r := Asc.p.
End WithExpressionR.
Module Type WithR. Parameter r : nat. End WithR.
Module Type HoldsR. Declare Module Held : WithR. End HoldsR.
Module AssumesInside. Module Asc : U := Assumes. Definition r := Asc.p. End AssumesInside.
(* AssumesInside is in the open, so the environment holds its field, which
   resolves to the axiom Assumes.p: the summary lists it in its own right. *)
Module OverType : HoldsR.
  Module Held : WithExpressionR := AssumesInside.
End OverType.
Definition over_type := OverType.Held.r.
