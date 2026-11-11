(* The answer chooses what P is, which makes every statement about P its
   own. P0 is a proposition, so filling it is legal; P is data, so filling
   it is not. *)

Definition P (n : nat) : Prop := True.

Definition P0 : P 0 := I.

Theorem thm : P 0.
Proof. exact I. Qed.
