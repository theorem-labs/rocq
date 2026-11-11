(* One of the image's own installed libraries: one file for both sides, read
   from the load path, bound by no -Q and pinned by no config. It declares a
   global universe that the task's statements stand on. *)

Monomorphic Universe b.

Monomorphic Definition Carrier : Type@{b} := nat.
