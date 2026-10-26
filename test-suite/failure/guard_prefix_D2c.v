(* A definition whose raw binder prefix carries a recursive call that the
   reduction erases before the analysis sees it. Accepted with a clean
   coqchk by the 9.2 member before its raw-prefix scan; evaluation does not
   terminate (Eval cbv overflows the stack). Found by the break attempt on
   the matching-term candidate. This branch's 9.3 parent
   (9.3/guard-uniform-bounds 30a1b2bbefca) already refuses it; the file
   pins that the rule here keeps refusing it.
   dispatch://BET-214 *)

(* D2c — chain of dead lets in the prefix; the first holds a non-decreasing
   outer call, the last pairs it with the inner fixpoint. *)
Definition outerD2c : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (d1 := outer (S (S p))).
    pose (d2 := d1).
    pose (d3 := (d2, inner)).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
Fail Defined.
Abort.
