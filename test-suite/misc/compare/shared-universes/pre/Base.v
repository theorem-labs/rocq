(* A shared library, as the standard library is: one file for both sides,
   read from the image and never staged. It declares a global universe that
   the task's statements stand on. *)

Monomorphic Universe b.

Monomorphic Definition Carrier : Type@{b} := nat.
