(* The same fully applied prefix call carried by a cast that the reduction
   removes. Must be refused: see guard_prefix_full_call.v. *)
Definition outer_bad_cast : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    refine (@eq_rect nat (inner O (S O)) (fun _ => nat -> nat -> nat) _ (inner O (S O)) eq_refl).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
  Fail Defined.
Abort.
