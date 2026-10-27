(* The second build of library Y: the same declarations, but [c] is proved
   with [ax2]. *)
Axiom ax1 : nat.
Axiom ax2 : nat.
Definition c : nat.
Proof. exact ax2. Qed.
