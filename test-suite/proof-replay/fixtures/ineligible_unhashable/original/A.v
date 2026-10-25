From Ltac2 Require Import Ltac2.

Set Default Proof Mode "Classic".

Ltac2 make_closure () := fun () => ().
Ltac2 use_closure () := let f := make_closure () in f ().

Lemma unhashable_proof : True.
Proof.
  ltac2:(use_closure ()).
  exact I.
Qed.
