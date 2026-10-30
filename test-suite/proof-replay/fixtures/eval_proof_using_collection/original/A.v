(* [same] declares the section variables of the collection C1 and [changed]
   those of C2. The edited tree changes C2, so [changed] must miss on that
   read; C1 does not change, so [same] must replay. *)
Section S.
Variables n m : nat.
Collection C1 := n.
Collection C2 := n.

Lemma same : True.
Proof using C1. exact I. Qed.

Lemma changed : True.
Proof using C2. exact I. Qed.
End S.
