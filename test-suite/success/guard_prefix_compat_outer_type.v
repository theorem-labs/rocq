(* The raw prefix holds a proof whose TYPE mentions the enclosing function,
   "let certificate := eq_refl : outer p = outer p in ...". The call [outer p]
   is on a structural subterm, so the analysis accepts it wherever it sits,
   and the definition terminates. Reported by the cross-family review of
   104624b79a as a false refusal: a rule that refuses every mention of a
   recursive function in the prefix, instead of submitting that mention to
   the analysis, loses this. *)
Definition compat_prefix_outer_type : nat -> nat.
Proof.
  fix outer 1.
  intro n.
  destruct n as [|p].
  - exact O.
  - refine ((_ : nat -> nat -> nat) p p).
    fix inner 2.
    pose (certificate := eq_refl : outer p = outer p).
    intros a m.
    destruct m as [|k].
    + exact (outer a).
    + exact (inner a k).
Defined.

Print Assumptions compat_prefix_outer_type.
Example compat_prefix_outer_type_computes : compat_prefix_outer_type 4 = 0 := eq_refl.
