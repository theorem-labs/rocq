(* writer's rewrite creates the rewriting scheme of myeq, which the proof
   term inlines. The scheme builder names the scheme's binders with
   Namegen.next_global_ident_away, which gives a name a suffix when it is a
   label of the module being built (Safe_typing.exists_objlabel). The edited
   tree declares HC before writer, so stock names a binder HC0 where the
   stored term holds HC: writer must miss on the objlabel read of HC, run,
   and write the object stock writes. The hit side of the channel is
   write_scheme_rewrite, whose proofs read the same names unchanged and
   replay. *)
Set Warnings "-missing-scheme".

Inductive myeq (A : Type) (x : A) : A -> Prop := myeq_refl : myeq A x x.

Lemma writer : forall x y : nat, myeq nat x y -> x = y.
Proof. intros x y H. rewrite H. reflexivity. Qed.
