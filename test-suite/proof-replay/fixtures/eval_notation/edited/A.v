(* [same] reads the notation [+++] and [changed] reads [***]. The edited
   tree changes what [***] means, so [changed] must miss on that read;
   [+++] does not change, so [same] must replay. No numerals: they read
   another channel (prim_token). *)
Notation "a +++ b" := (andb a b) (at level 50, left associativity).
Notation "a *** b" := (orb a b) (at level 40, left associativity).

Lemma same : bool.
Proof. exact (true +++ false). Qed.

Lemma changed : bool.
Proof. exact (false *** true). Qed.
