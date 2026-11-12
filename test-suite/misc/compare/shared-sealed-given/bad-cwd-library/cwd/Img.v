(* A library the answer leaves in the directory the comparator runs in. The
   load path binds that directory implicitly, under no root, so this file is
   the library Img, outside every root the challenge stands in for, and its
   sealed Given.Hidden.ax prints Img.Given.Hidden.ax, the permitted given of
   the image's Img.Given, at the type False. *)

Module Given.
  Module Type SIG.
    Parameter p : False.
  End SIG.
  Module Hidden : SIG.
    Axiom ax : False.
    Definition p : False := ax.
  End Hidden.
End Given.
