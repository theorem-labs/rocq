(* The same two declarations, but [f] is a different type here. The two
   blocks read the same, and the constant their constructor mentions has
   the same short name in both files; only its definition differs. *)
Definition f : Set := bool.

Inductive t := C : f -> t.

Theorem thm : forall x : t, x = x.
Proof. reflexivity. Qed.
