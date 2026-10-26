Require Import Setoid.

Parameter f g : nat -> nat.
Axiom fg : forall n, f n = g n.

Create Rewrite HintDb db.
#[export] Hint Rewrite <- fg : db.

Lemma lstrat : f 0 = g 0.
Proof. rewrite_strat (topdown (hints db)). reflexivity. Qed.

Lemma lauto : f 0 = g 0.
Proof. autorewrite with db. reflexivity. Qed.
