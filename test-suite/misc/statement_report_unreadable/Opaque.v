(* [model]'s closure reaches [secret], whose body is opaque, so the report must
   READ that body from the library's table of opaque proofs. The test makes that
   read fail, which is what a damaged table, or a lazy reader refusing a table
   whose bytes changed since intern, does to it. *)

Lemma secret : nat.
Proof. exact 0. Qed.

Definition model : nat := secret.
