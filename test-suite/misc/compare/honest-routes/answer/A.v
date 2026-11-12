(* The honest answer reaches the shared library's axiom, and the given
   through an alias of its module, after a Require Export and an Import,
   which change no kernel name. *)

Require Img.Classical.
Require Export Top.P.Q.
Import Top.P.Q.

Module N' := Top.P.Q.N.

Theorem thm : (0 = 1 \/ ~ 0 = 1) /\ 0 = 1.
Proof.
  split; [exact (Img.Classical.classic _) | exact (False_rect _ N'.j)].
Qed.
