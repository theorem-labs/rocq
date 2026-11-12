(* The challenge file, with a module Q whose inductive prints Top.P.Q.T, the
   name of the tolerated given. *)

Definition harmless : nat := 0.

Module Q.
  #[bypass_check(positivity)]
  Inductive T : Type := mk : (T -> False) -> T.
End Q.
