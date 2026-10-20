(** The axiom elimination sits several real binders (a [let] and a [match]
    branch) below the proof's root: the goal has to be cooked at exactly that
    depth, since a section-discharged reference inside it must land on the
    same [Rel] a real cooking pass, which does walk from the root, would
    produce. *)

Axiom bad : False.

Section S.
  Variable u : nat.
  Definition k := u + 1.
  Lemma usedin_nestedmatch : k = k.
  Proof.
    exact (
      let n := 0 in
      match n with
      | O => match bad return k = k with end
      | S _ => match bad return k = k with end
      end).
  Qed.
End S.

Print Assumptions usedin_nestedmatch.
