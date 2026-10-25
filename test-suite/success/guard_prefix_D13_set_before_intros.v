(* D13 — same, with [set] instead of [pose].  Terminating and computing. *)

Definition outerD13 : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    set (rec := inner).
    intros a m.
    destruct m as [|k].
    + exact (outer p).
    + exact (rec a k).
Defined.

Print Assumptions outerD13.
Example d13_computes : outerD13 5 = 0. Proof. reflexivity. Qed.
