(* fresh "foo" gives foo0 when foo is a keyword. The edited tree makes foo a
   keyword after t, so clear foo fails there and lfresh is fun _ => false,
   where the registration's term is fun _ => true. The string literal is not
   reparsed, so the proof's sentences are equal: only the keyword read can
   refuse the stored term. lbar asks fresh about another string, which the
   edit does not touch. No numerals: their recorded interpretation holds
   their source position. *)

Ltac t := let x := ident:(foo) in first [ clear x; exact true | exact false ].

Lemma lfresh : nat -> bool.
Proof. let H := fresh "foo" in intro H. t. Qed.

Lemma lbar : nat -> bool.
Proof. let H := fresh "bar" in intro H. exact true. Qed.
