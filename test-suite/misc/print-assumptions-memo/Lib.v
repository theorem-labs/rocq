(* Compiled with -vos by the script, so [hidden]'s body is not available to
   a client checked with -vok. *)

Axiom axiom : nat.

Lemma hidden : nat.
Proof. exact axiom. Qed.

Lemma shown : nat.
Proof. exact axiom. Defined.
