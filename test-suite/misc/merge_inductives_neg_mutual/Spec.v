(* One mutual block of two types. Neither mentions the other, so that the
   agent can declare the same two types apart and the block itself is the only
   difference. *)
Inductive even := E0 : even | ES : even -> even
with odd := OS : odd -> odd.

Definition Stmt := forall x : even, x = x.
