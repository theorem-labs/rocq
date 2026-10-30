(* [same] runs the Ltac2 definition t1 and [changed] runs t2. The edited tree
   changes the body of t2, so [changed] must miss on that read; t1 does not
   change, so [same] must replay. *)
From Ltac2 Require Import Ltac2.

Ltac2 t1 () := exact I.
Ltac2 t2 () := constructor.

Lemma same : True.
Proof. t1 (). Qed.

Lemma changed : True.
Proof. t2 (). Qed.
