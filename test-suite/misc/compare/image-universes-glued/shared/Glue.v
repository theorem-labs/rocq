(* The image itself relates v and w, so the answer's proof needs nothing the
   challenge's own environment does not already stand on. *)

Require Img.V.
Require Img.W.

Monomorphic Constraint Img.V.v < Img.W.w.
