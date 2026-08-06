Definition restricted_model_identity (A : Type) (x : A) : A := x.

Example restricted_model_identity_nat : restricted_model_identity nat 0 = 0.
Proof.
  reflexivity.
Qed.
