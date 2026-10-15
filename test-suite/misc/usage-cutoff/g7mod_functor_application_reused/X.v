Module Type S.
  Parameter n : nat.
End S.
Module F (Y : S).
  Definition m := Y.n.
End F.
Module Arg.
  Definition n := 5.
End Arg.
Module M := F Arg.
