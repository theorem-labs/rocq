(* p asks Ltac2 for the absolute name of c (Env.path, a reverse lookup in
   the global nametab) and asserts that it has 3 parts: PR, A and c. The
   edited tree moves the definition of c from just before Section S to just
   inside it. Its kernel name stays PR.A.c, so the forward lookup of c finds
   the same reference, but its absolute name becomes PR.A.S.c. p's key does
   not change: not its statement, its sentences or its position. Stock now
   fails the assertion, so replay must not install the stored term
   (cross-family review of 079bc4cb71, finding CF2, trigger T2). *)
From Ltac2 Require Import Ltac2.

Section S.
Definition c := O.

Lemma p : True.
Proof.
  let r := List.hd (Env.expand [@c]) in
  Control.assert_true (Int.equal (List.length (Env.path r)) 3).
  exact I.
Qed.

End S.
