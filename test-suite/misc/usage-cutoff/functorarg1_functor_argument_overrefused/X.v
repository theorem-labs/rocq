Module Type S.
  Parameter y : nat.
End S.
Module F (P : S).
  Include P.
  Definition f := 1.
End F.
