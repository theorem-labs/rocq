(* The same fully applied prefix call, one local definition deeper. Must be
   refused: see guard_prefix_full_call.v. *)
Definition outer_bad_nested_let : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (dead := let also_dead := inner O (S O) in also_dead).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
  Fail Defined.
Abort.
