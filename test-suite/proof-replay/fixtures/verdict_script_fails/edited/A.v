(* The goal is provable only through the hint: `auto` closes `True` on its
   own, which would make the edited tree compile and the fixture vacuous. *)
Parameter P : Prop.
Axiom p_holds : P.

Create HintDb db.

Lemma by_hint : P.
Proof. auto with db. Qed.
