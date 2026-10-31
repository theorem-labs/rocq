(* [same] unfolds the constant the notation GG names and [changed] the one FF
   names. The edited tree makes FF stand for g instead of f, so [changed] must
   miss on that read. The two unfolds leave different goals, so the term the
   registration stored for [changed] is not the stock term: a hit there gives
   another object. GG does not change, so [same] must replay. *)
Definition f (n : nat) := n.
Definition g (n : nat) := n.
Declare Scope a_scope.
Notation "'FF' x" := (g x) (at level 10) : a_scope.
Notation "'GG' x" := (g x) (at level 10) : a_scope.

Lemma same : f 0 = g 0.
Proof. unfold "GG". reflexivity. Qed.

Lemma changed : f 0 = g 0.
Proof. unfold "FF". reflexivity. Qed.
