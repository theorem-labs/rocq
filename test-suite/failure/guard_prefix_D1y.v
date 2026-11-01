(* A definition whose raw binder prefix carries a call to the ENCLOSING
   fixpoint. The scan that catches calls to the inner block s own members
   missed this one, and this branch's earlier head accepted it with a clean
   coqchk; Eval cbv overflows the stack. dispatch://BET-214 *)

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
