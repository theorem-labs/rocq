(* bad-own-constraint's forgery, moved one root over: the file that asserts
   the constraint sits under a second bound root, Vendor, which no checked
   library lives under, so the challenge directory does not stand in for it.
   Were such a library taken for one of the image's, the challenge would
   load it too and the constraint would be in both graphs -- a file the
   answer wrote deciding what the challenge stands on. The comparator
   refuses the run instead, because the config pins nothing under that
   root. *)

Require Vendor.Glue.

Definition unused := Img.Third.Yet.
