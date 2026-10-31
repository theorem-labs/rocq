(* The edited tree gives f a bidirectionality hint (Arguments f n & b)
   before l. l elaborates an application of f under an expected type, so it
   reads f's hint; the hint changed, so l must miss on that read. control
   reads no hint and hits. *)
Definition f (n : nat) (b : bool) : bool := b.
Arguments f n & b.
Lemma l : bool.
Proof. exact (f O true). Qed.

Lemma control : True.
Proof. exact I. Qed.
