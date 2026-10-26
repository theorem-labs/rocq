(* The same hole with the erased position the argument of a beta redex whose
   binder the body never reads. Accepted by the 9.2 release febc57ac52, by
   the cut d9061a3408 and by this branch's 9.3 parent (9.3/guard-uniform-bounds
   30a1b2bbefca, "Closed under the global context", coqchk -o -norec exit 0),
   with `Eval cbv in (top_dead_beta 3)` dying with "Stack overflow". *)
Definition top_dead_beta : nat -> nat.
Proof.
  fix f 1.
  refine ((fun _ : nat => _) (f (S O))).
  intro m.
  destruct m as [|p].
  - exact O.
  - exact (f p).
  Fail Defined.
Abort.
