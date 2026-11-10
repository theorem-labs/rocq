(* An image library that relates two levels the challenge already knows. The
   challenge's statements do not Require it; the answer does, as an agent's
   proof Requires more of the standard library than the statement file it was
   given. Its constraint is the image's, not the answer's. *)

Require Img.Base.
Require Img.Extra.

Monomorphic Constraint Img.Base.b < Img.Extra.e.
