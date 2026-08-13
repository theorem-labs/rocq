Axiom premise : Prop.
Axiom witness : premise.
Axiom unused : Prop.

Definition transparent_witness : premise := witness.

Inductive wrapper : Type := wrap : premise -> wrapper.

Theorem through_transparent : premise.
Proof. exact transparent_witness. Qed.

Theorem closed : True.
Proof. exact I. Qed.

Theorem uses_wrapper : wrapper -> wrapper.
Proof. exact (fun value => value). Qed.
