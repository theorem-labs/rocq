Require Pre.Base.
Require Pre.Extra.

Monomorphic Definition stmt : Type@{Pre.Base.b} := Pre.Base.Carrier.
Monomorphic Definition stmt2 : Type@{Pre.Extra.e} := Pre.Extra.Other.

Theorem thm : stmt = Pre.Base.Carrier.
Proof. reflexivity. Qed.
