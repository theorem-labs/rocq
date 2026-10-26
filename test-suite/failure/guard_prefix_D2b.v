(* A definition whose raw binder prefix carries a recursive call that the
   reduction erases before the analysis sees it. Accepted with a clean
   coqchk by the 9.2 member before its raw-prefix scan, and accepted by
   this branch's 9.3 parent (9.3/guard-uniform-bounds 30a1b2bbefca);
   evaluation does not terminate (Eval cbv overflows the stack). Found by
   the break attempt on the matching-term candidate.
   dispatch://BET-214 *)

(* D2b — dead beta argument under a cast in the prefix, holding a
   non-decreasing outer call. *)
Definition outerD2b : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    refine (((fun (_ : nat) (a m : nat) => _) (outer (S (S p)))
             : nat -> nat -> nat)).
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
Fail Defined.
Abort.
