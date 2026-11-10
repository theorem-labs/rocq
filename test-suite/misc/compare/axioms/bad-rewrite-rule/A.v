(* A rewrite rule, which the config does not permit. *)

Definition two := 2.

Symbol raise : forall (A : Type), A.

Rewrite Rule raise_nat := raise nat => 0.

Lemma given : two = 2.
Proof. reflexivity. Qed.

Theorem thm : two = 2.
Proof. reflexivity. Qed.
