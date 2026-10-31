(* Each proof asks Ltac2 for the absolute name of a constant (Env.path, a
   reverse lookup in the global nametab). The edited tree moves c from just
   before Section S to just inside it: c keeps its kernel name, and its
   absolute name gains S. [changed] reads the name of c and must miss on the
   xreftab/to_path read. [same] reads the name of d, which does not change,
   and must replay. Neither proof asserts anything, so both compiles
   succeed. *)
From Ltac2 Require Import Ltac2.

Definition d := O.
Section S.
Definition c := O.

Lemma same : True.
Proof.
  let _ := Env.path (List.hd (Env.expand [@d])) in
  exact I.
Qed.

Lemma changed : True.
Proof.
  let _ := Env.path (List.hd (Env.expand [@c])) in
  exact I.
Qed.

End S.
