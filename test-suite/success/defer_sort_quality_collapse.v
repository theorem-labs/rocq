Set Universe Polymorphism.
Set Primitive Projections.
Set Polymorphic Inductive Cumulativity.
Unset Collapse Sorts ToType.
Set Allow StrictProp.

Record bar {A} (a : A) : Prop := { }.

Definition bar1 : bar I := ltac:(constructor).
Fail Check bar1@{SProp;}.
Definition bar2 : bar@{Prop;Set} I := ltac:(constructor).

Set Printing All.
Set Printing Universes.

Check eq_refl : bar1 = bar2.
