(** [Context] with an implicit binder: the section variable it introduces is
    discharged exactly like an explicit [Variable], so a reference to a
    constant depending on it has to be cooked the same way in the "used in"
    type. *)

Axiom bad : False.

Section S.
  Context {u : nat}.
  Definition k := u + 1.
  Lemma usedin_context : k = k.
  Proof. exact (match bad return k = k with end). Qed.
End S.

Print Assumptions usedin_context.
