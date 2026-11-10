(* Spec.v's block with one constructor more. *)

Inductive color := Red | Green | Blue.

Theorem thm : forall c : color, c = c.
Proof. reflexivity. Qed.

Definition b : color := Blue.

Lemma b_ne_red : b <> Red.
Proof. discriminate. Qed.

Lemma b_ne_green : b <> Green.
Proof. discriminate. Qed.
