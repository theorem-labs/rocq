(* Control for failure/guard_prefix_sibling.v: the same mutual inner block,
   built the same way, whose prefix definition mentions nothing recursive.
   The rule must keep accepting it, so that the refusal of the sibling call
   next door says something. Accepted by the 9.3 base and by this commit,
   each with "Closed under the global context". dispatch://BET-241 *)
Definition outer_sib_ok : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix a 2 with (b (x m : nat) {struct m} : nat).
    + pose (dead := 0).
      intros x m.
      destruct m as [|k].
      * exact (outer x).
      * exact (a x k).
    + intros x m.
      destruct m as [|k].
      * exact (outer x).
      * exact (b x k).
Defined.
Print Assumptions outer_sib_ok.
