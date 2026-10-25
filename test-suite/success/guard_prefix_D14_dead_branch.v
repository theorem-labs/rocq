(* D14 — blast radius.  The nested fixpoint with the prefix binding sits in
   a branch of a match on [O] that is never taken.  The guard checker visits
   every branch, so the bail-out refuses the whole definition from a branch
   that cannot run.  Terminating and computing. *)

Definition outerD14 : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine (match O with
            | O => outer p
            | S _ => (_ : nat -> nat -> nat) p p
            end).
    fix inner 2.
    pose (dead := inner).
    intros a m.
    destruct m as [|k].
    + exact O.
    + exact (inner a k).
Defined.

Print Assumptions outerD14.
Example d14_computes : outerD14 5 = 0. Proof. reflexivity. Qed.
