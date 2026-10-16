Require Import A.
Module X : T.
  Module D.
    Definition w := 1.
  End D.
End X.
Definition b := X.D.w.
