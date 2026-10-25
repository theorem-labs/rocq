(* D2 — D1 with the prefix binding USED by the body, so the term is not
   dead code.  After zeta the analysed body contains [inner a k] exactly as
   in D0/D1, so the analysis measures the same uniform prefix of 1; the
   rewriting still meets the bare occurrence in the prefix and bails.
   Terminating and computing, as D0. *)

Definition outerD2 : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (self := inner).
    intros a m.
    destruct m as [|k].
    + exact (outer p).
    + exact (self a k).
Defined.

Print Assumptions outerD2.
Example d2_computes : outerD2 5 = 0. Proof. reflexivity. Qed.
