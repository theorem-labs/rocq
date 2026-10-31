(* [unfold "FF"] names a constant through a notation: the tactic searches
   every scope for a notation FF that stands for a reference. The edited tree
   adds a second such notation, in a scope that is not open, for another
   constant. No open scope chooses between the two, so stock fails with
   "Unable to unambiguously interpret "FF" as a reference". Replay must fail
   too: no other read of the proof sees the new notation (gate review, breadth
   audit gap BA2). *)
Definition f (n : nat) := n.
Definition g (n : nat) := n.
Declare Scope a_scope.
Declare Scope b_scope.
Notation "'FF' x" := (f x) (at level 10) : a_scope.
Notation "'FF' x" := (g x) (at level 10) : b_scope.

Lemma p : f 0 = 0.
Proof. unfold "FF". reflexivity. Qed.
