(* Spec.v's block word for word, declared coinductively, which makes it
   inhabited. *)

CoInductive stream := Cons : nat -> stream -> stream.

Theorem thm : forall x : stream, x = x.
Proof. reflexivity. Qed.

CoFixpoint zeros : stream := Cons 0 zeros.
