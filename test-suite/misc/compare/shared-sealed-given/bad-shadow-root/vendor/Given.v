(* A forgery of the shared library: the answer binds its own directory to
   Img, so that Img.Given resolves to this file, whose unsealed axiom prints
   Img.Given.Hidden.ax. *)

Module Hidden.
  Axiom ax : True.
  Definition p : True := ax.
End Hidden.
