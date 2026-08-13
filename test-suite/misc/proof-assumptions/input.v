Axiom premise : Prop.
Axiom witness : premise.
Axiom unused : Prop.

Symbol rewrite_symbol : premise.

Definition transparent_witness : premise := witness.

Inductive wrapper : Type := wrap : premise -> wrapper.

Module Type SealedSignature.
  Parameter hidden : premise.
End SealedSignature.

Module SealedImplementation : SealedSignature.
  Definition hidden : premise := witness.
End SealedImplementation.

Theorem through_transparent : premise.
Proof. exact transparent_witness. Qed.

Theorem closed : True.
Proof. exact I. Qed.

Theorem uses_wrapper : wrapper -> wrapper.
Proof. exact (fun value => value). Qed.

Theorem through_sealed : premise.
Proof. exact SealedImplementation.hidden. Qed.

Theorem through_symbol : premise.
Proof. exact rewrite_symbol. Qed.
