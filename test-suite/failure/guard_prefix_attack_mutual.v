(* The same fully applied prefix call inside a MUTUAL inner block, in the
   body that is not the one selected. Must be refused: see
   guard_prefix_full_call.v. *)
Definition outer_bad_mutual : nat -> nat.
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
        with inner2 (a m : nat) {struct m} : nat :=
          let dead := inner2 O (S O) in
          match m with
          | O => outer a
          | S k => inner2 a k
          end
        for inner1) p p).

Abort.
