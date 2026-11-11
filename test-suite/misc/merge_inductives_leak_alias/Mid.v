Require Spec.
Require Agent.

(* A name reached through an alias: its user half is Mid.A.tree and its
   canonical half is whatever the merge left, so it is the one shape the
   export step cannot undo by looking the user half up. *)
Module A := Agent.

Definition d := A.Leaf.
