(* The bidirectionality hint of a variable, read under its name: [same]
   applies its hypothesis HC, [changed] applies the section variable HD. The
   edited tree gives HD a hint (Arguments HD _ & _), so [changed] must miss on
   that read; HC's (none) does not change, so [same] must replay. *)
Section S.
Variable HD : nat -> bool -> bool.
Arguments HD _ & _.
Lemma same (HC : nat -> bool -> bool) : bool.
Proof. exact (HC O true). Qed.

Lemma changed : bool.
Proof. exact (HD O true). Qed.
End S.
