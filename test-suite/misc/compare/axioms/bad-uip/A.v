(* Definitional UIP: a relaxed typing flag the config does not tolerate. *)

Definition two := 2.

Set Definitional UIP.

Inductive seq {A : Type} (a : A) : A -> SProp := srefl : seq a a.

Unset Definitional UIP.

Lemma given : two = 2.
Proof. reflexivity. Qed.

Definition uip_use (x : nat) (h : seq x x) : two = 2 :=
  match h in seq _ y return y = y -> two = 2 with
  | srefl _ => fun _ => eq_refl
  end eq_refl.

Theorem thm : two = 2.
Proof. exact (uip_use 0 (srefl 0)). Qed.
