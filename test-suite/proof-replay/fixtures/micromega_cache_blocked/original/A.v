(* The grading engine makes the four micromega cache paths directories
   before the first compile, in the registration and in the grade (tree_dirs
   here). No table can open, so every lookup runs the prover, and the
   micromega_cache fence finds no file. The edited tree adds an unrelated
   definition, and both proofs replay. *)
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma by_nia (x y : Z) : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof. intros. nia. Qed.

Lemma by_lia (x y : Z) : 2 * x + 3 * y = 5 -> x >= 0 -> y >= 0 -> x <= 2.
Proof. intros. lia. Qed.
