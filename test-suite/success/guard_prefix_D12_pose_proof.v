(* D12 — the same regression reached by naming the induction hypothesis,
   which is an ordinary thing to do in a [fix] proof:
     fix inner 2.  pose proof inner as IH.  intros a m. ...
   Terminating and computing. *)

Definition outerD12 : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose proof inner as IH.
    intros a m.
    destruct m as [|k].
    + exact (outer p).
    + exact (IH a k).
Defined.

Print Assumptions outerD12.
Example d12_computes : outerD12 5 = 0. Proof. reflexivity. Qed.
