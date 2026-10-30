(* [same] uses the abbreviation a1 and [changed] uses a2. The edited tree
   changes what a2 stands for, so [changed] must miss on that read; a1 does
   not change, so [same] must replay. *)
Notation a1 := (fun x : bool => x).
Notation a2 := (fun x : bool => negb (negb x)).

Lemma same : bool.
Proof. exact (a1 true). Qed.

Lemma changed : bool.
Proof. exact (a2 true). Qed.
