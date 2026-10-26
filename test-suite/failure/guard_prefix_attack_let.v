(* A fully applied recursive call in the inner fixpoint's raw binder prefix,
   held by a local definition. Must be refused: see guard_prefix_full_call.v
   for why dropping arguments there instead is unsound. *)
Definition outer_bad_let : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (dead := inner O (S O)).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
  Fail Defined.
Abort.
