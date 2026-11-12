(* The forged Top.P.Q.thm of P.v and the real one of the pre-checked P/Q.v
   are both in this answer's environment: the pre-checked library is loaded
   whatever the answer Requires. So whenever a forgery prints the theorem's
   name, the theorem is declared twice under it, and the run fails on that.
   The verdict must also read the real constant by its kernel name, not the
   forged one: its axioms are the admitted Top.P.Q.thm itself, where the
   forged [I] would have none (expected-reason checks both). An answer
   without the real constant fails as missing; this suite cannot build one
   with a same-printed forgery, because a pre-checked library is always
   loaded and a challenge file is a top-level library of the tree. *)

Require Top.P.

Definition uses : 0 = 1 -> True := fun _ => I.
