(* coq-prog-args: ("-skip-qed-typecheck" "-async-proofs" "on") *)

Lemma bad : False.
Proof. exact_no_check I. Qed.
