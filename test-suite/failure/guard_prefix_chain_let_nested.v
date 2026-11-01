(* Nested fixpoint. A call of the ENCLOSING function on a BIGGER argument
   sits in a let read only by a second, dead let in the inner prefix. The
   release-7 cut 18da2c8ff497 checks the dead value "x" (a let variable) and
   never the value of x: it accepts the definition with "Closed under the
   global context" and `coqchk -o -norec` exit 0, and `Eval cbv` on it
   overflows the stack (Port90's bug-finder file f6). The nested prefix walk
   now substitutes the live let, and the call "outer (S (S p))" reaches the
   analysis. Ported from 9.0/guard-cofix-prefix 9e24663c6e07.
   dispatch://BET-214 *)
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
