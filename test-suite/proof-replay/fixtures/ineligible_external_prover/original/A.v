From Stdlib Require Import ZArith Psatz Lia.

Lemma control : True.
Proof. exact I. Qed.

Lemma external_proof (x : Z) : (0 <= x * x)%Z.
Proof. first [psatz Z 2 | nia]. Qed.
