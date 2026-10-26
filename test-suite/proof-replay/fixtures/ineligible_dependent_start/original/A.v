From Corelib Require Import derive.Derive.

Derive f in (f = 3) as f_eq.
Proof. subst f. reflexivity. Qed.
