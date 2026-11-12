(* The rule is inside a module sealed by a type that shows its symbol as a
   parameter, so the environment outside the module holds neither a symbol
   nor a rule. The module's body was still checked with the rule in
   place, and l rests on it. *)

Module Type T.
  Parameter s : nat.
  Parameter l : s = 0.
End T.

Module M : T.
  Symbol s : nat.
  Rewrite Rule r := s => 0.
  Definition l : s = 0 := eq_refl.
End M.

Definition two := 2.

Theorem thm : two = 2.
Proof. reflexivity. Qed.
