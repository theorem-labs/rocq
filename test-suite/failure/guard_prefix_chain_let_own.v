(* Nested fixpoint calling ITSELF on a constructor argument from its own
   prefix, through a let read only by a second, dead let. The inner block's
   own check on the release-7 cut 18da2c8ff497 (raw_prefix_escapes) sees
   only "Rel 1" in the dead value and accepts the definition with "Closed
   under the global context" and `coqchk -o -norec` exit 0, and `Eval cbv`
   on it overflows the stack (Port90's bug-finder file f6b). The walk now
   follows the live let and sees "inner O (S O)" in the dead one. Ported
   from 9.0/guard-cofix-prefix 9e24663c6e07. dispatch://BET-214 *)
Definition outer_own_chain : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (x := inner O (S O)).
    pose (y := x).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
Fail Defined.
Abort.
