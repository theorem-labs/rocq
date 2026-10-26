Axiom B : Prop.
Axiom hb : B.
#[export] Hint Resolve hb : db1.
Lemma l : B.
Proof. auto with db1. Qed.
