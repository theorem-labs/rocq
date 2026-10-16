Module Type T2.
  Parameter w : nat.
End T2.
Module Type T.
  Declare Module D : T2.
  Parameter z : nat.
End T.
