(* Top-level MUTUAL block: the second body calls the first from its prefix
   through the let chain of guard_prefix_chain_let_top.v. The release-7 cut
   18da2c8ff497 accepts it with "Closed under the global context" and
   `coqchk -o -norec` exit 0 (Port90's bug-finder file f8). Ported from
   9.0/guard-cofix-prefix 9e24663c6e07. dispatch://BET-214 *)
Definition mut_chain : nat -> nat.
Proof.
  fix f 1 with (g (n : nat) {struct n} : nat).
  - intro n. destruct n as [|p]. + exact O. + exact (g p).
  - pose (x := f (S O)).
    pose (y := x).
    intro n. destruct n as [|p]. + exact O. + exact (f p).
Fail Defined.
Abort.
