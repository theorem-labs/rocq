(* [same] finds its value through the canonical instances of carrier1, and
   [changed] through those of carrier2. The edited tree declares one more
   canonical instance of S2 (S2_unit, defined in both trees), so the table
   [changed] reads is not the one it read at registration: [changed] must
   miss on that read. The instances of carrier1 do not change, so [same]
   must replay. *)
Structure S1 := { carrier1 : Type; elt1 : carrier1 }.
Structure S2 := { carrier2 : Type; elt2 : carrier2 }.

Canonical Structure S1_nat := {| carrier1 := nat; elt1 := O |}.
Canonical Structure S2_bool := {| carrier2 := bool; elt2 := true |}.
Definition S2_unit := {| carrier2 := unit; elt2 := tt |}.
Canonical S2_unit.

Lemma same : nat.
Proof. exact (elt1 _). Qed.

Lemma changed : bool.
Proof. exact (elt2 _). Qed.
