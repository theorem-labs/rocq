(* A tolerated flag with no object: the kind wherever it appears.

   An honest proof of an equality reaches Corelib.Init.Logic.eq, an
   inductive of the image built without -indices-matter, so its closure
   carries indices-not-mattering on an object the task never wrote. The
   route the comparator replaces always allowed that kind, on any object
   (grading-tools _axiom_kinds._ALWAYS_ALLOWED_KINDS); naming every object
   of the image that carries it would be a list of the standard library.

   fail-config is the other half: a kind-only entry for ANOTHER kind
   tolerates nothing of this one, and the same honest answer fails under
   it. *)

Theorem thm : forall n : nat, n = n.
Proof.
Admitted.
