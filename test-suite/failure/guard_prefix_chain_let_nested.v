(* Red on the release-7 rule (accepted, coqchk 0, Eval cbv overflows the stack); stock Rocq 9.0.1 refuses it with "Recursive call to outer has principal argument equal to ...". The nested prefix walk now substitutes the live let, so the call reaches the analysis. dispatch://BET-214 *)
(* Nested fixpoint. A call of the ENCLOSING function on a BIGGER argument
   sits in a let read only by a second, dead let in the inner prefix.
   check_erased_prefix checks the dead value "x" (a let variable) and
   never the value of x. *)
Definition outer_chain : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (x := outer (S (S p))).
    pose (y := x).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
Fail Defined.
Abort.
