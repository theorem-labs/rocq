(* The other direction of verdict_firstorder_coercion: the edited tree removes
   the coercion W. firstorder then unfolds [W n] and builds another term, so
   [changed] must miss on the coercion table and give stock's .vo. [same] runs
   no firstorder, reads no coercion, and still replays (gate review, breadth
   audit gap BA3). *)
Definition W (n : nat) : Prop := n = 0 \/ n = 1.
Coercion W : nat >-> Sortclass.

Lemma same : forall n, W n -> W n.
Proof. intros n H. exact H. Qed.

Lemma changed : forall n, W n -> W n \/ False.
Proof. firstorder auto. Qed.
