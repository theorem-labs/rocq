Require Img.Base.
Require Img.Extra.
Require Img.Third.

Monomorphic Definition stmt : Type@{Img.Base.b} := Img.Base.Carrier.
Monomorphic Definition stmt2 : Type@{Img.Extra.e} := Img.Extra.Other.
Monomorphic Definition stmt3 : Type@{Img.Third.t} := Img.Third.Yet.

Theorem thm : stmt = Img.Base.Carrier.
Proof.
Admitted.
