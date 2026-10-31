(* In each proof, [exact eq_refl] refines the function evar ?f into a lambda
   whose binder takes the name reserved for its type, read from the reverse
   reserved-type table: bool in [same], nat in [changed]. The edited tree
   reserves m instead of n for nat, so [changed] must miss on that read. The
   name reserved for bool does not change, so [same] must replay. *)
Implicit Types n : nat.
Implicit Types b : bool.

Lemma same (c : bool) : exists f : bool -> bool, f true = c.
Proof. eexists. exact eq_refl. Qed.

Lemma changed (k : nat) : exists f : nat -> nat, f 1 = k.
Proof. eexists. exact eq_refl. Qed.
