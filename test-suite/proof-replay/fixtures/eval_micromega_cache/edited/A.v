(* Both trees block .nia.cache with a directory, as the grading engine
   does. The registration tree blocks .lia.cache too, so no table opens
   there and both proofs are eligible. The edited tree holds a .lia.cache
   instead, the one a compile of this tree writes (tree_files). No table has
   opened it when the grade decides [same], so the micromega_cache fence
   trips there, and neither proof replays. [changed]'s tactics then find
   their certificate in the cache, and both runs compile. *)
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma same (x y : Z) : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof. intros. nia. Qed.

Lemma changed (x y : Z) : 2 * x + 3 * y = 5 -> x >= 0 -> y >= 0 -> x <= 2.
Proof. lia. Qed.
