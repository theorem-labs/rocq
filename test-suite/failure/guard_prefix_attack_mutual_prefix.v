(* guard_prefix_attack_mutual.v puts its dead call after both binders of
   inner2, so it is not in the binder prefix and any Rocq refuses it as an
   ordinary guard error. Here the same fully applied call sits in the binder
   PREFIX of inner2, the body of the mutual inner block that is not the one
   selected: a local definition between a and the structural argument m, which
   the body never reads. Reduction erases it before the guard analysis, so
   only the erased-prefix rule sees the call; it must be refused, because the
   call would be refused had the reduction kept it (its structural argument
   S O is not a subterm). *)
Definition outer_bad_mutual_prefix : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - Fail exact
      ((fix inner1 (a m : nat) {struct m} : nat :=
          match m with
          | O => outer a
          | S k => inner1 a k
          end
        with inner2 (a : nat) (dead : nat := inner2 O (S O)) (m : nat) {struct m} : nat :=
          match m with
          | O => outer a
          | S k => inner2 a k
          end
        for inner1) p p).
Abort.
