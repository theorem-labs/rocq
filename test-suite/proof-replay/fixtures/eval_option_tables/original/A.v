(* The contents of every Goptions table (the sets that Add and Remove
   change, Keep Equalities among them) are one start-of-proof read,
   option_tables. The edited tree removes the Add between the two proofs.
   changed's injection reads that entry: with it the proof term holds the
   injected equality, without it injection fails and try skips it. changed
   must miss on the option_tables read, and same, which starts before the
   Add and reads the unchanged table, must replay. *)
Inductive bar : Prop := bar_1.
Inductive baz : Prop := baz_1.
Add Keep Equalities bar.

Lemma same : forall a b : bar, Some a = Some b -> a = b.
Proof. intros a b H. injection H as E. exact E. Qed.

Add Keep Equalities baz.

Lemma changed : forall a b : baz, Some a = Some b -> True.
Proof. intros a b H. try injection H. intros. exact I. Qed.
