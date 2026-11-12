(* The honest answer proves thm from the tolerated given. *)

Require Top.P.
Require Top.P.Q.

Theorem thm : False.
Proof.
  pose (f := fun t : Top.P.Q.T => match t with Top.P.Q.mk g => g t end).
  exact (f (Top.P.Q.mk f)).
Qed.
