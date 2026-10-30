(* warm runs congruence while core.eq.type is bool, which forces
   congruence's process-wide equality reference to bool; its fallback proves
   the goal. Reset anchor restores the equality registration, not that
   reference: in later, congruence still uses bool, the assertion fails, and
   the fallback proves True, so stock accepts later. A replay of warm would
   leave the reference unforced, and later would force it to eq. So Reset is
   a late command, and warm runs. Both trees are the same. *)
Definition anchor := tt.
Register bool as core.eq.type.

Lemma warm : forall x : nat, x = x.
Proof.
  intros x.
  first [congruence | exact (@eq_refl nat x)].
Qed.

Reset anchor.

Lemma later : True.
Proof.
  first
    [ assert (H : forall x : nat, x = x) by congruence;
      fail 1 "unexpected congruence success"
    | exact I ].
Qed.
