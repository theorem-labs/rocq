(* D1 — D0 plus ONE local definition in the inner fixpoint's binder prefix,
   written with "pose" before "intros", which is what an ordinary tactic
   proof produces.  The function is unchanged: it still terminates and still
   computes to the same value.

   The uniform-parameter analysis never sees the binding, because it works on
   the body after split_struct_arg has stripped and reduced the prefix away.
   drop_uniform_parameters walks the body as written, meets the bare
   occurrence, and (since 8928f01bdb85) bails out, so the definition is
   REFUSED.  The 9.2 release and stock Rocq 9.2.0 bound the prefix at that
   same occurrence (their analysis walks the raw body), get 0, rewrite
   nothing, and ACCEPT. *)

Definition outerD1 : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (dead := inner).
    intros a m.
    destruct m as [|k].
    + exact (outer p).
    + exact (inner a k).
Defined.

Print Assumptions outerD1.
Example d1_computes : outerD1 5 = 0. Proof. reflexivity. Qed.
