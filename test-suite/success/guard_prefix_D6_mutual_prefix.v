(* D6 — two mutually recursive inner fixpoints, with the bare occurrence in
   the binder prefix of the SECOND body.  The bail-out is called as
   [bail () = illformed i], where [i] is the index of the fixpoint being
   checked, not the index of the body whose rewriting failed, so the
   diagnostic names the wrong body.  Terminating and computing. *)

Definition outerD6 : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner1 2 with (inner2 (a m : nat) {struct m} : nat).
    + intros a m.
      destruct m as [|k].
      * exact (outer p).
      * exact (inner2 a k).
    + pose (dead := inner1).
      intros a m.
      destruct m as [|k].
      * exact O.
      * exact (inner2 a k).
Defined.

Print Assumptions outerD6.
Example d6_computes : outerD6 5 = 0. Proof. reflexivity. Qed.
