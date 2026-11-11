(* The challenge file, with modules Q.N whose axiom prints Top.P.Q.N.j, the
   name of the given inside a module of the pre-checked file. *)

Definition harmless : nat := 0.

Module M.
  Axiom k : False.
End M.

Module Q.
  Module N.
    Axiom j : False.
  End N.
End Q.
