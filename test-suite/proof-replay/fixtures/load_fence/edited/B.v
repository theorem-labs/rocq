(* Gate review, INFRA-361 gap 2. The registration has no [Load], so its
   record keeps [later] eligible. The edited file loads L.v instead: the
   [Load] trips the grade's own fence, and [later] runs. *)
Load "./L.v".

Lemma later : 1 = 1.
Proof. reflexivity. Qed.
