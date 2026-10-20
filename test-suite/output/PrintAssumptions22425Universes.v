(** Same cooking, for a universe-polymorphic section constant: the discharge
    both applies the constant to the section variable it closes over and
    substitutes its universe instance, printed with and without the levels
    ([Set Printing Universes]). *)

Set Universe Polymorphism.
Axiom bad : False.

Section P.
  Universe w.
  Variable T : Type@{w}.
  Definition pk := T -> T.
  Lemma usedin_univ : pk = pk.
  Proof. exact (match bad return pk = pk with end). Qed.
End P.

Print Assumptions usedin_univ.
Set Printing Universes.
Print Assumptions usedin_univ.
