From Ltac2 Require Import Ltac2.

Ltac2 t () := constructor.

Lemma l : True.
Proof. t (). Qed.
