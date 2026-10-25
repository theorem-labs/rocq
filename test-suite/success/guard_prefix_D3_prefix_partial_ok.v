(* D3 — a three-argument inner fixpoint, so the computed uniform prefix is
   2, and a prefix binding that is a PARTIAL application of the inner
   fixpoint (one argument, which is fewer than 2).  Terminating and
   computing.  The bail-out does not test for a bare occurrence, it tests
   the argument count, so a partial application reaches it too. *)

Definition outerD3 : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat -> nat) p p p).
    fix inner 3.
    pose (part := inner O).
    intros a b m.
    destruct m as [|k].
    + exact (outer p).
    + exact (inner a b k).
Defined.

Print Assumptions outerD3.
Example d3_computes : outerD3 5 = 0. Proof. reflexivity. Qed.
