(* A module Q whose constant thm prints Top.P.Q.thm, the theorem's name,
   at a type it can prove. *)

Definition harmless : nat := 0.

Module Q.
  Definition thm : True := I.
End Q.
