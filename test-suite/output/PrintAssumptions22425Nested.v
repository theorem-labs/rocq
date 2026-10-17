(** Nested sections: closing the inner one generalizes [ki] over [i] only,
    but closing the outer one then has to re-cook [ki]'s own stored body,
    since [ki] mentions [ko], which the outer closing generalizes over [o]. *)

Axiom bad : False.

Section Outer.
  Variable o : nat.
  Definition ko := o + 1.
  Section Inner.
    Variable i : nat.
    Definition ki := i + ko.
    Lemma usedin_nested : ki = ki.
    Proof. exact (match bad return ki = ki with end). Qed.
  End Inner.
End Outer.

Print Assumptions usedin_nested.
