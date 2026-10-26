(** The [admit] tactic (the empty match on [Stdlib.Compat.AdmitAxiom.admit])
    hits this bug's pattern; the [Admitted] command creates a bare named
    axiom with no empty match at all, and was never on the uncooked path at
    all ([get_constant_body] never even looks at it). Both forms, side by
    side, on the same section-discharged constant. *)

Axiom bad : False.

Section S.
  Variable u : nat.
  Definition k := u + 1.
  Lemma usedin_admit_tactic : k = k.
  Proof. admit. Admitted.
  Lemma usedin_admitted_command : k = k.
  Proof. Admitted.
End S.

Print Assumptions usedin_admit_tactic.
Print Assumptions usedin_admitted_command.
