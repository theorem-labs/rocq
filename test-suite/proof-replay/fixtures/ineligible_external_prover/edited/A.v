From Stdlib Require Import ZArith Psatz Lia.

Definition pad := 0.

Lemma control : True.
Proof. exact I. Qed.

Lemma external_proof (x : Z) : (0 <= x * x)%Z.
Proof. first [psatz Z 2 | nia]. Qed.
