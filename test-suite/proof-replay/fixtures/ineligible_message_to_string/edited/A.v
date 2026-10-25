From Ltac2 Require Import Ltac2.

Set Default Proof Mode "Classic".

Definition pad := 0.

Ltac2 message_to_string () :=
  let _ := Message.to_string (Message.of_string "proof replay") in ().

Lemma message_proof : True.
Proof.
  ltac2:(message_to_string ()).
  exact I.
Qed.
