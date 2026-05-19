Set Universe Polymorphism.
Set Primitive Projections.
Set Polymorphic Inductive Cumulativity.
Unset Collapse Sorts ToType.

Record bar {A} (a : A) : Prop := { }.

Definition bar1 : bar I := ltac:(constructor).
Definition bar2 : bar@{Prop;Set} I := ltac:(constructor).

Set Printing All.
Set Printing Universes.

Check eq_refl : bar1 = bar2.
