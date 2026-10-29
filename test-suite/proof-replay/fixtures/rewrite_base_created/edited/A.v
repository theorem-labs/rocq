(* The registration has no rewrite base db, so autorewrite fails and labsent
   is false; its record holds the base as absent. The edited tree creates db
   empty, so autorewrite succeeds and labsent is true. A replay must see the
   base appear and refuse the stored false. Create Rewrite HintDb moves no
   counter. control reads no base and hits. *)
Create Rewrite HintDb db.
Lemma labsent : bool.
Proof. tryif autorewrite with db then exact true else exact false. Qed.

Lemma control : True.
Proof. exact I. Qed.
