(* [unfold "FF"%a] searches only a_scope, where two notations FF stand for a
   reference. When several match, the one whose notation the open scopes give
   to a_scope wins: b_scope is opened last and holds FF x, so [FF x] belongs to
   b_scope and only [FF x y] (f2) is left. The edited tree removes FF x from
   b_scope. Then both notations of a_scope are left, the name is ambiguous and
   the stock script fails. Nothing in a_scope changes and the scope stack is the
   same, so replay must read the scope each notation gets (gate review, breadth
   audit gap BA2). *)
Definition f (n : nat) := n.
Definition f2 (n m : nat) := n.
Definition g (n : nat) := n.
Declare Scope a_scope.
Delimit Scope a_scope with a.
Declare Scope b_scope.
Notation "'FF' x" := (f x) (at level 10, x at level 9) : a_scope.
Notation "'FF' x y" := (f2 x y) (at level 10, x at level 9, y at level 9) : a_scope.
Open Scope a_scope.
Open Scope b_scope.

Lemma p : f2 0 0 = 0.
Proof. unfold "FF"%a. reflexivity. Qed.
