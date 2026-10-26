(* The let chain of guard_prefix_chain_let_top.v in the second body of a top-level mutual block. Red on the release-7 rule (accepted, coqchk 0). dispatch://BET-214 *)
(* Top-level MUTUAL block: the second body calls the first from its prefix
   through the let chain of f3. *)
Definition mut_chain : nat -> nat.
Proof.
  fix f 1 with (g (n : nat) {struct n} : nat).
  - intro n. destruct n as [|p]. + exact O. + exact (g p).
  - pose (x := f (S O)).
    pose (y := x).
    intro n. destruct n as [|p]. + exact O. + exact (f p).
Fail Defined.
Abort.
