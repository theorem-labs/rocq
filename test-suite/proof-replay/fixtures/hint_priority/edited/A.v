Axiom B : Prop.
Axiom hb : B.
Axiom hb' : B.
#[export] Hint Resolve hb | 4 : db1.
#[export] Hint Resolve hb' | 2 : db1.
Lemma l : B.
Proof. auto with db1. Qed.
