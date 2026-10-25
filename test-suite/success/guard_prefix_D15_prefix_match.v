(* D15 — the unanalysed region is not only local definitions: it is whatever
   the prefix reduction erases.  Here the inner fixpoint's body is a match on
   [O] whose taken branch is the real body and whose other branch is a bare
   occurrence of the fixpoint.  split_struct_arg iota-reduces the match away,
   so the analysis never sees the second branch; the rewriting walks it.

   This is also the shape that would show the "assert false" in
   check_nested_fix_body reachable, if dropping arguments could change which
   branch the prefix reduces to.  It cannot: the branch is selected by [O].
   Terminating and computing. *)

Definition outerD15 : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    refine (match O return nat -> nat -> nat with
            | O => _
            | S _ => inner
            end).
    intros a m.
    destruct m as [|k].
    + exact (outer p).
    + exact (inner a k).
Defined.

Print Assumptions outerD15.
Example d15_computes : outerD15 5 = 0. Proof. reflexivity. Qed.
