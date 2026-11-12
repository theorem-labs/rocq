(* A file of the task the answer leaves unchanged, so the config declares it
   pre-checked, as the grader does. It holds two givens: Top.P.Q.g, and
   Top.P.Q.N.j inside a module. *)

Axiom g : False.

Module N.
  Axiom j : False.
End N.
