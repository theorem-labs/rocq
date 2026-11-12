(* A library of the image's own, which challenge and answer both load from
   one file and the config does not pre-check. Its given Img.Given.Hidden.ax
   is a field of a sealed module that the signature does not export: only
   the implementation of Hidden.p reaches it. *)

Module Type SIG.
  Parameter p : True.
End SIG.

Module Hidden : SIG.
  Axiom ax : True.
  Definition p : True := ax.
End Hidden.
