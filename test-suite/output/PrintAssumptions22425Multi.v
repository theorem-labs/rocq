(** A goal that mentions several section-discharged constants at once: every
    one of them has to be cooked in the printed type, not just the first. *)

Axiom bad : False.

Section S.
  Variable u : nat.
  Definition k1 := u + 1.
  Definition k2 := u + 2.
  Definition k3 := u + 3.
  Lemma usedin_multi : k1 + k2 = k3.
  Proof. exact (match bad return k1 + k2 = k3 with end). Qed.
End S.

Print Assumptions usedin_multi.
