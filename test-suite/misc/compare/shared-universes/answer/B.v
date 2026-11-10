(* The agent's own file, which Requires one more of the image's libraries
   than the statement file does. Img.Glue relates two of the levels the
   statements stand on, and the challenge files' own Require lines never
   reach it, so the answer's universe graph holds a constraint the
   challenge's closure does not. The answer did not assert it: the image
   did, and the challenge loads the same shared libraries the answer loaded,
   so the constraint is in both graphs and no theorem fails for it. *)

Require Img.Glue.

Definition unused := Img.Extra.Other.
