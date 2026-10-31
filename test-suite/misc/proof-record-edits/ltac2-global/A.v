From Ltac2 Require Import Ltac2.

Ltac2 t () := exact I.

Lemma l : True.
Proof. t (). Qed.
