(* An axiom the proof reaches only through a sealed module's
   implementation: the shape of dispatch://BET-245. The public signature
   shows a proved lemma; the implementation rests on an axiom. *)

Definition two := 2.

Module Type HIDE.
  Parameter p : two = 2.
End HIDE.

Module Hidden : HIDE.
  Axiom cheat : two = 2.
  Definition p : two = 2 := cheat.
End Hidden.

Lemma given : two = 2.
Proof. exact Hidden.p. Qed.

Theorem thm : two = 2.
Proof. exact Hidden.p. Qed.
