(* -proof-replay names a record file that does not exist. The file must
   compile as stock does, with every proof run by its tactics. *)
Lemma p : forall n : nat, n + 0 = n.
Proof. intros n. induction n as [|n IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma q : 2 + 2 = 4.
Proof. reflexivity. Qed.
