(* Top-level fixpoint. The call sits in a let that the prefix walk calls
   live because a SECOND let reads it; that second let is dead, so the
   reduction erases both. On the release-7 cut 18da2c8ff497,
   raw_prefix_escapes sees only "Rel 1" in the dead value and the definition
   is accepted with "Closed under the global context" and `coqchk -o -norec`
   exit 0, and `Eval cbv` on it overflows the stack (Port90's bug-finder
   file f3). The prefix walk now follows a let whose binder is read, as head
   reduction does. Ported from 9.0/guard-cofix-prefix 9e24663c6e07.
   dispatch://BET-214 *)
Definition top_chain : nat -> nat.
Proof.
  fix f 1.
  pose (x := f (S O)).
  pose (y := x).
  intro n.
  destruct n as [|p].
  - exact O.
  - exact (f p).
Fail Defined.
Abort.
