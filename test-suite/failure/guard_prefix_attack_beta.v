(* The same fully applied prefix call as the argument of a beta redex that
   discards it. Must be refused: see guard_prefix_full_call.v. *)
Definition outer_bad_beta : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    refine ((fun _ : nat => _) (inner O (S O))).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
  Fail Defined.
Abort.
