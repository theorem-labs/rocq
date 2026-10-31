(* A.v and B.v run this file with [Load]; it is not compiled on its own.
   Its proof opens and closes inside the [Load] sentence. *)
Definition k := 1 + 2.

Lemma inner : True.
Proof. exact I. Qed.
