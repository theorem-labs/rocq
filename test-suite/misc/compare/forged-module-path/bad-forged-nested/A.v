Require Top.P.

Theorem thm : 0 = 1 /\ 1 = 2 /\ 2 = 3.
Proof.
  split; [exact (False_rect _ Top.P.Q.N.j) |].
  split; [exact (False_rect _ Top.P.Q.N.j) | exact (False_rect _ Top.P.M.k)].
Qed.
