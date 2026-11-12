(* Rocq does not load the library Top.P.Q beside a module Top.P.Q, so this
   answer requires only Top.P, and Top.P.Q.T is its own inductive. *)

Require Top.P.

Theorem thm : False.
Proof.
  pose (f := fun t : Top.P.Q.T => match t with Top.P.Q.mk g => g t end).
  exact (f (Top.P.Q.mk f)).
Qed.
