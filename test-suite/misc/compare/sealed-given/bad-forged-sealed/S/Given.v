(* A file of the task the answer leaves unchanged, so the config declares it
   pre-checked, as the grader does. Its given Top.S.Given.Hidden.ax is a
   field of a sealed module that the signature does not export: only the
   implementation of Hidden.p reaches it. *)

Module Type SIG.
  Parameter p : True.
End SIG.

Module Hidden : SIG.
  Axiom ax : True.
  Definition p : True := ax.
End Hidden.
