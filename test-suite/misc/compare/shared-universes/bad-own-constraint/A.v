Require Pre.Base.
Require Pre.Extra.
Require Pre.Third.

Monomorphic Definition stmt : Type@{Pre.Base.b} := Pre.Base.Carrier.
Monomorphic Definition stmt2 : Type@{Pre.Extra.e} := Pre.Extra.Other.
Monomorphic Definition stmt3 : Type@{Pre.Third.t} := Pre.Third.Yet.

Theorem thm : stmt = Pre.Base.Carrier.
Proof. reflexivity. Qed.
