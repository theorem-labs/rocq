(* Printing Reversible Up To Unification / Conversion Modulo Universes /
   Conversion: printing options get progressively turned on until the
   printed form re-parses and re-elaborates to an equal term. *)

(* Baseline: no check, hidden arguments are not re-inferable from the
   printed form alone. *)
Check @eq_refl nat 0.

(* Unification is enough to re-infer the hidden arguments from the
   original term, so nothing needs to be made explicit. *)
Set Printing Reversible Up To Unification.
Check @eq_refl nat 0.

(* Standalone re-elaboration of [eq_refl] leaves unresolved holes, so
   implicit arguments get printed. *)
Set Printing Reversible Up To Conversion.
Check @eq_refl nat 0.

(* The three flags behave like a radio button. *)
Test Printing Reversible Up To Unification.
Test Printing Reversible Up To Conversion.

(* Universe instances: re-elaboration introduces a fresh flexible
   universe. Unifying it with the original instance is fine up to
   conversion modulo universes, but not up to strict conversion, which
   requires the instance to be printed. *)
Polymorphic Definition pid@{u} (A : Type@{u}) (a : A) := a.
Universe u.
Check pid@{u}.
Set Printing Reversible Up To Conversion Modulo Universes.
Check pid@{u}.
Set Printing Reversible Up To Unification.
Check pid@{u}.

(* Unsetting the active flag turns the check off entirely. *)
Unset Printing Reversible Up To Unification.
Check @eq_refl nat 0.

(* A printing-only notation that does not print what it parses is
   detected and bypassed by turning notations off. *)
Set Printing Reversible Up To Unification.
Module LyingNotation.
  Notation "x ** y" := (Nat.mul x y) (at level 40).
  Set Warnings "-notation-overridden".
  Notation "x ** y" := (Nat.add x y) (at level 40, only printing).
  Check 2 * 3.
  Check 2 + 3.
End LyingNotation.

(* Goal display is checked too. *)
Set Printing Reversible Up To Conversion.
Goal @eq_refl nat 0 = eq_refl.
Show.
Abort.

(* Sort universes of [Check Type] cannot be re-parsed at all (their
   names are not declared), so a warning is emitted and the most
   explicit form is printed. *)
Check Type.

(* Sort variables (sorts rung variant): under strict conversion the
   anonymized universe levels of the sort-structure display do not
   check, so full universes get printed; the laxer modes accept the
   default display. *)
Sort s.
Axiom S : Type@{s;Set}.
Check S.
Set Printing Reversible Up To Conversion Modulo Universes.
Check S.
