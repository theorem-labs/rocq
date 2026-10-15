Require Import X.
Require Import A.
Module Type Q.
  Include T.
End Q.
Module R : Q.
  Definition f := 1.
End R.
