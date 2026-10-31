Axiom B : Prop.
Axiom hb : B.
#[export] Hint Extern 0 B => exact hb : db1.
Lemma l : B.
Proof. auto with db1. Qed.
