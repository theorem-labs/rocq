(* The same fully applied prefix call in the branch of a match on a
   constructor that is already decided. Must be refused: see
   guard_prefix_full_call.v. *)
Definition outer_bad_match : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    refine (match O with O => _ | S _ => fun _ _ => inner O (S O) end).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
  Fail Defined.
Abort.
