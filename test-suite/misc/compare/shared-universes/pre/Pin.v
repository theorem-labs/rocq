(* A library the CONFIG can pin, under a bound root rather than the image's
   load path. It carries the constraint bad-own-constraint asserts, between
   two of the levels the statements stand on.

   The case's own config does not pin it, so no run loads it. fail-config's
   does, which puts it on the admit list and so into the ANSWER's
   environment -- and a pre-checked library is not a shared one, so the
   challenge does not load it and the honest answer fails under that config.
   A config pins bytes; it cannot decide what the challenge stands on. *)

Require Img.Base.
Require Img.Third.

Monomorphic Constraint Img.Base.b < Img.Third.t.
