(* The same constraint as Pre.Glue's, asserted by a file of the answer's own
   tree rather than carried by a shared library. The challenge does not stand
   on it, and the answer's statements do, so this answer proves less than the
   challenge asks and must fail. *)

Require Pre.Base.
Require Pre.Extra.

Monomorphic Constraint Pre.Base.b < Pre.Extra.e.
