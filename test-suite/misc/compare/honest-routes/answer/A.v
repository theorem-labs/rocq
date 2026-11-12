(* The honest answer reaches the shared library's axiom, and the given
   through an alias of its module and through a module that includes it,
   after a Require Export and an Import, which change no kernel name. *)

Require Img.Classical.
Require Export Top.P.Q.
Import Top.P.Q.

Module N' := Top.P.Q.N.

Module I.
  Include Top.P.Q.N.
End I.

Theorem thm : (0 = 1 \/ ~ 0 = 1) /\ 0 = 1 /\ 1 = 2.
Proof.
  split; [exact (Img.Classical.classic _) |].
  split; [exact (False_rect _ N'.j) | exact (False_rect _ I.j)].
Qed.
