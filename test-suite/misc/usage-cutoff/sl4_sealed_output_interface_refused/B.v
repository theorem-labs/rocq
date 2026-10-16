Require Import A.
Module X : T.
  Definition x := 1.
  Definition w := 0.
End X.
Definition b := X.x.
