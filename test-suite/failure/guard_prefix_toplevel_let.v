(* A fully applied recursive call in the binder prefix of a TOP-LEVEL
   fixpoint, held by a local definition the body never reads. The rule that
   refuses it for a fixpoint nested in a body did not reach this one, and
   every 9.2 we have accepts it, as does this branch's 9.3 parent
   (9.3/guard-uniform-bounds 30a1b2bbefca): `coqc` prints "Closed under the
   global context", `coqchk -o -norec` exits 0, and
   `Eval cbv in (top_dead_let 3)` then dies with "Stack overflow", because
   the dead call increases its argument. *)
Definition top_dead_let : nat -> nat.
Proof.
  fix f 1.
  pose (dead := f (S O)).
  intro n.
  destruct n as [|p].
  - exact O.
  - exact (f p).
  Fail Defined.
Abort.
