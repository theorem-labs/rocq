(* Each proof reduces a beta redex with a named reduction (Declare
   Reduction), which is a read on channel red_expr keyed by the name. The
   edited tree changes rchanged and rinner to cbv beta iota, which gives the
   same result, and declares rlate. [changed] must miss on the read of
   rchanged. [nested] names rnested, whose expression is the name rinner:
   the read of rnested does not change, the read of rinner does, so it must
   miss. [absent] tries rlate, which the original tree does not declare: the
   absence is the read's value, and it must miss when rlate appears. [same]
   reads rsame, which does not change, and must replay. Every Declare comes
   before the first Qed: a later one is a late command. *)
Declare Reduction rsame := cbv beta.
Declare Reduction rchanged := cbv beta.
Declare Reduction rinner := cbv beta.
Declare Reduction rnested := rinner.

Lemma same : forall n : nat, n = n.
Proof.
  intro n.
  let t := eval rsame in ((fun x : nat => x) n) in
  exact (eq_refl t).
Qed.

Lemma changed : forall n : nat, n = n.
Proof.
  intro n.
  let t := eval rchanged in ((fun x : nat => x) n) in
  exact (eq_refl t).
Qed.

Lemma nested : forall n : nat, n = n.
Proof.
  intro n.
  let t := eval rnested in ((fun x : nat => x) n) in
  exact (eq_refl t).
Qed.

Lemma absent : True.
Proof.
  try (let t := eval rlate in ((fun x : nat => x) 0) in idtac).
  exact I.
Qed.
