(** The "used in" diagnostic prints the goal an axiom was eliminated to prove
    verbatim, so a reference to a section-discharged constant inside that
    goal has to appear the way the discharge would print it: the constant
    applied to the section variable it was generalized over. Walking the
    proof's stored (uncooked) term for speed, rather than the fully
    discharged (cooked) one, must not leave that application off. *)

Axiom bad : False.

Section S.
  Variable u : nat.
  Definition k := u + 1.
  Lemma usedin_arg : k = k.
  Proof. exact (match bad return k = k with end). Qed.
End S.

Print Assumptions usedin_arg.
