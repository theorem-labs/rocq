Axiom B : Prop.
Axiom hb : B.

(* A comment and a blank line move the hint down; it does the same. *)

#[export] Hint Resolve hb : db1.
Lemma l : B.
Proof. auto with db1. Qed.
