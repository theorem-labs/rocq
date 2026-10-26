Ltac t := let x := ident:(foo) in first [ clear x; exact 1 | exact 0 ].
Reserved Notation "x 'foo' y" (at level 50).
Lemma lfresh : nat -> nat.
Proof. let H := fresh "foo" in intro H. t. Qed.
