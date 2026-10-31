(* [assert (H : PP)] interprets PP as a type, in the scope that Bind Scope
   attaches to Sortclass. The edited tree binds Sortclass to b_scope, where
   PP has no interpretation, so the stock script fails. Replay must fail
   too: the recorded notation query names a_scope, which still answers, so
   only a read of the scope that Sortclass selects sees the edit (gate
   review, breadth audit gap BA1). *)
Declare Scope a_scope.
Declare Scope b_scope.
Notation "'PP'" := True : a_scope.
Bind Scope a_scope with Sortclass.

Lemma p : True.
Proof. assert (H : PP) by exact I. exact H. Qed.
