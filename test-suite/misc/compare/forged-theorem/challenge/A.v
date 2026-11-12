(* The verdict reads the theorem Top.P.Q.thm. A module Q of the library
   Top.P holding a constant thm prints the same name, so the comparator
   must read the theorem by the challenge's kernel name, and refuses an
   answer that holds two constants printing it. *)

Require Top.P.
Require Top.P.Q.

Definition uses : 0 = 1 -> True := fun _ => I.
