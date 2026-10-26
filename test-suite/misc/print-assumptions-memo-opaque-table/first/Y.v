(* The first build of library Y: [c] is proved with [ax1]. *)
Axiom ax1 : nat.
Axiom ax2 : nat.
Definition c : nat.
Proof. exact ax1. Qed.
