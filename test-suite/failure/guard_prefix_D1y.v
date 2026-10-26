(* A definition whose raw binder prefix carries a call to the ENCLOSING
   fixpoint. The scan that catches calls to the inner block s own members
   missed this one, and an earlier head of the 9.2 member accepted it with a
   clean coqchk; this branch's 9.3 parent (9.3/guard-uniform-bounds
   30a1b2bbefca) accepts it too. Eval cbv overflows the stack.
   dispatch://BET-214 *)

(* D1y — the D1 carrier under cbv only. *)
Definition outerD1 : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (dead := outer (S (S p))).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
  Fail Defined.
Abort.
