(* Red on the release-7 rule (9.2/guard-cofix-prefix 891c0f336dec): compiled, coqchk -o -norec 0, and Eval cbv overflows the stack. The prefix walk now substitutes a let whose binder is read, as head reduction does. dispatch://BET-214 *)
(* Top-level fixpoint. The call sits in a let that the prefix walk calls
   live because a SECOND let reads it; that second let is dead, so the
   reduction erases both. raw_prefix_escapes sees only "Rel 1" in the
   dead value. *)
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
