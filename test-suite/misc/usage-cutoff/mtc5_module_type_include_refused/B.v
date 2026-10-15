Require Import A.
Module X.
  Include T.
End X.
Definition b : nat := X.x.
