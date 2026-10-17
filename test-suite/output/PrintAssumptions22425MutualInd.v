(** A mutual inductive that the section discharge generalizes: the PR's own
    bailout ([uncooked_opaque_table] returns [None] whenever the discharge
    generalized any inductive, since a stored [Case] node then has fewer
    parameters than the discharged inductive declares) already routes this
    through the cooked [force_proof] fallback, unaffected by this fix. Kept
    as a regression check that the fallback still matches stock exactly. *)

Axiom bad : False.

Section S.
  Variable T : Type.
  Inductive mutA : Type :=
  | ca : T -> mutB -> mutA
  | ca0 : mutA
  with mutB : Type :=
  | cb : T -> mutA -> mutB
  | cb0 : mutB.

  Lemma usedin_mutual : mutA = mutA.
  Proof. exact (match bad return mutA = mutA with end). Qed.
End S.

Print Assumptions usedin_mutual.
