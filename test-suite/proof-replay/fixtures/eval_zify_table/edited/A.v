(* [same] and [changed] each run zify_op, which reads the three zify tables.
   Between the two proofs one operator is registered with zify: my_one in the
   original tree, my_zero in the edited one. So the operator table [changed]
   reads is not the one it read at registration, and [changed] must miss on
   that read. [same] reads the tables before the registration and must
   replay. Both trees register one operator of the same kind there, so the
   universe counters at [changed] are the same in both. *)
From Stdlib Require Import ZArith ZifyClasses ZifyInst Zify.

Definition my_zero : Z := Z0.
Definition my_one : Z := Zpos xH.

#[global] Instance Op_my_zero : CstOp my_zero := { TCst := Z0 ; TCstInj := eq_refl }.
#[global] Instance Op_my_one : CstOp my_one := { TCst := Zpos xH ; TCstInj := eq_refl }.

Lemma same (x : Z) : x = x.
Proof. zify_op. exact eq_refl. Qed.

Add Zify CstOp Op_my_zero.

Lemma changed (x : Z) : x = x.
Proof. zify_op. exact eq_refl. Qed.
