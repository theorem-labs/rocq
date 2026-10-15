Fixpoint f (n : nat) : nat :=
  match n with
  | O => O
  | S n' => f n'
  end.
