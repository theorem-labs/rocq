From Corelib Require Import derive.Derive.

Definition pad := 0.

Derive f in (f = 3) as f_eq.
Proof. subst f. reflexivity. Qed.
