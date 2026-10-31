(* Gate review, INFRA-361 gap 2: see the edited B.v. Here [inner] is written
   in the file, so the record keeps it eligible. *)
Definition k := 3.

Lemma inner : True.
Proof. exact I. Qed.
