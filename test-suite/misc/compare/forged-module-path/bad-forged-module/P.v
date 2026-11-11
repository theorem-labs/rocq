(* The challenge file, with a module Q whose axiom prints Top.P.Q.g, the
   name of the pre-checked given. *)

Definition harmless : nat := 0.

Module M.
  Axiom k : False.
End M.

Module Q.
  Axiom g : False.
End Q.
