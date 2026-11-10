(* A constraint between two of the levels the statements stand on, asserted
   by a file of the answer's OWN tree rather than carried by a library of the
   image. No image library relates Img.Base.b and Img.Third.t, so the
   challenge does not stand on it and the answer does: this answer proves
   less than the challenge asks, and must fail. *)

Require Img.Base.
Require Img.Third.

Monomorphic Constraint Img.Base.b < Img.Third.t.
