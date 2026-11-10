(* A shared library that relates two levels the challenge already knows. The
   challenge's statements do not Require it; the answer does, as an agent's
   proof Requires more of the standard library than the statement file it was
   given. Its constraint is the image's, not the answer's. *)

Require Pre.Base.
Require Pre.Extra.

Monomorphic Constraint Pre.Base.b < Pre.Extra.e.
