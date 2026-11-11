(* Rocq does not load the library Top.P.Q beside a module Top.P.Q, so this
   answer requires only Top.P, and Top.P.Q.g is its own axiom. *)

Require Top.P.

Theorem thm : 0 = 1 /\ 1 = 2 /\ 2 = 3.
Proof.
  split; [exact (False_rect _ Top.P.Q.g) |].
  split; [exact (False_rect _ Top.P.Q.g) | exact (False_rect _ Top.P.M.k)].
Qed.
