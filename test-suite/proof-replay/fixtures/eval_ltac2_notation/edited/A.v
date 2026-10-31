(* [same] uses the Ltac2 notation solve1 and [changed] uses solve2. The edited
   tree changes what solve2 expands to, so [changed] must miss on that read;
   solve1 does not change, so [same] must replay. *)
From Ltac2 Require Import Ltac2.

Ltac2 Notation "solve1" := exact I.
Ltac2 Notation "solve2" := constructor.

Lemma same : True.
Proof. solve1. Qed.

Lemma changed : True.
Proof. solve2. Qed.
