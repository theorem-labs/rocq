(* An ordinary terminating nested fixpoint whose raw prefix binds a match
   pattern variable: "let seed := p in ...". [p] is a structural subterm and
   a function of neither recursive block, so the prefix rule must accept it.
   Reported by the cross-family review of 104624b79a as a false refusal. *)
Definition compat_prefix_local : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (seed := p).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
Defined.

Print Assumptions compat_prefix_local.
Example compat_prefix_local_computes : compat_prefix_local 4 = 0 := eq_refl.
