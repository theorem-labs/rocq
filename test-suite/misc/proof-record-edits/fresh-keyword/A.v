Ltac t := let x := ident:(foo) in first [ clear x; exact 1 | exact 0 ].

Lemma lfresh : nat -> nat.
Proof. let H := fresh "foo" in intro H. t. Qed.
