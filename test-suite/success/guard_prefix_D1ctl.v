(* The binder-prefix rule must not refuse a prefix that holds a HARMLESS
   value. Here the dead local definition is [S p], where [p] is a match
   pattern variable and no recursive function at all. An earlier version of
   the rule counted the length of the subterm-specification list, which
   covers every local in scope, and refused this. *)
Definition outerD1c : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (dead := S p).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
Defined.

Print Assumptions outerD1c.
Example d1ctl_computes : outerD1c 3 = 0 := eq_refl.
