(* Expected time < 0.50s *)

From Corelib Require Import BinNums PosDef.

Fixpoint ones (n : nat) : positive :=
  match n with
  | O => xH
  | S n' => xI (ones n')
  end.

Time Definition square_ones := Eval vm_compute in Pos.mul (ones 15000) (ones 15000).
