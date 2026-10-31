(* `rewrite` with a user equality creates its rewriting scheme on demand
   (tactics/ind_tables.ml define, census row M4) and raises `missing-scheme`.
   `induction` and `inversion` create no scheme in this tree: with
   `Unset Elimination Schemes` they fail with "Cannot find the elimination
   combinator bit_ind", so this is the fixture for the scheme write. A proof
   that raises a warning is not replayed, so the warning is disabled here:
   the fixture is about the scheme. *)
Set Warnings "-missing-scheme".

Inductive myeq (A : Type) (x : A) : A -> Prop := myeq_refl : myeq A x x.

Definition pad := 1.

Lemma writer : forall x y : nat, myeq nat x y -> x = y.
Proof. intros x y H. rewrite H. reflexivity. Qed.

Lemma later_reader : forall x y : nat, myeq nat x y -> x = y.
Proof. intros x y H. rewrite H. reflexivity. Qed.
