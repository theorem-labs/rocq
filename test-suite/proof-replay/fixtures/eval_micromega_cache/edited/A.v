(* Each lookup in a micromega cache reads, keyed by the cache file, what the
   table loaded when it was opened. Both trees block .nia.cache with a
   directory, as the grading engine does, so [same] reads no entry at the
   registration and at the grade, and must replay. The registration tree
   blocks .lia.cache too. The edited tree holds a .lia.cache instead, the one
   a compile of this tree writes (tree_files), so [changed] reads the digest
   of its bytes where it read no entry, and must miss on that read. Its
   tactics then find their certificate in the cache, and both runs compile. *)
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma same (x y : Z) : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof. intros. nia. Qed.

Lemma changed (x y : Z) : 2 * x + 3 * y = 5 -> x >= 0 -> y >= 0 -> x <= 2.
Proof. lia. Qed.
