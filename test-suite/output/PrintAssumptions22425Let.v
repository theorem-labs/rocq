(** A section [Let]: it discharges to a local definition in every constant
    that uses it, so the "used in" type has to show the let-bound occurrence
    cooked exactly like any other section-local reference. *)

Axiom bad : False.

Section S.
  Variable u : nat.
  Let la := u + 1.
  Lemma usedin_let : la = la.
  Proof. exact (match bad return la = la with end). Qed.
End S.

Print Assumptions usedin_let.
