(* The escaped name reaches the declarations array: this answer changes
   that definition's body, so its record names it. *)

Definition deux : nat := 2.

Definition théorème_ÿ : nat := 2.

Theorem thm : théorème_ÿ = 2.
Proof. reflexivity. Qed.
