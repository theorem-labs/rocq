From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma first (x y : Z) : 0 <= x -> 0 <= y -> 0 <= x + y.
Proof. lia. Qed.

Lemma second (x y : Z) : 0 <= x -> x <= y -> 0 <= y.
Proof. lia. Qed.
