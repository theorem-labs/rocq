(* [same] binds b and [changed] binds c without a type, so each reads its
   reserved type (Implicit Types). The edited tree gives c another (still
   convertible) reserved type, so [changed] must miss on that read; b's does
   not change, so [same] must replay. The new type makes no unification
   variable, so the evar counter at each proof is the same in both trees. *)
Implicit Types b : bool.
Implicit Types c : bool.

Lemma same : bool -> bool.
Proof. exact (fun b => b). Qed.

Lemma changed : bool -> bool.
Proof. exact (fun c => c). Qed.
