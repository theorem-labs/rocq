(* A constraint between two of the levels the statements stand on, asserted
   by a file of the answer's OWN tree rather than carried by a shared
   library. No shared library relates Pre.Base.b and Pre.Third.t, so the
   challenge does not stand on it and the answer does: this answer proves
   less than the challenge asks, and must fail. *)

Require Pre.Base.
Require Pre.Third.

Monomorphic Constraint Pre.Base.b < Pre.Third.t.
