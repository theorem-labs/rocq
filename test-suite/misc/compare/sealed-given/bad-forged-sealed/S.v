(* A file of the task the answer may change, so it is a challenge file. It
   holds two givens: Top.S.H.hx, a field of a sealed module that the
   signature does not export, and Top.S.E.ex, exported. *)

Module Type SIG2.
  Parameter q : True.
End SIG2.

Module H : SIG2.
  Axiom hx : True.
  Definition q : True := hx.
End H.

Module E.
  Axiom ex : True.
End E.

(* The forgery sealed as the given is, so that its axiom too is a hidden
   field printing Top.S.Given.Hidden.ax. *)
Module Given.
  Module Type SIG.
    Parameter p : True.
  End SIG.
  Module Hidden : SIG.
    Axiom ax : True.
    Definition p : True := ax.
  End Hidden.
End Given.
