(* [exact eq_refl] unifies [?f 1] with the variable k. The argument 1 is not
   a variable, so unification refines the function evar ?f into a lambda
   (Evardefine.evar_absorb_arguments). The lambda's binder has no name in the
   evar's type (nat -> nat), so it takes the name that Implicit Types reserves
   for nat, read from the reverse reserved-type table: n here, m in the edited
   tree. The proof term holds that name, so the stock object differs from the
   registered one, and replay must give the stock object (gate review of
   079bc4cb71, CF6). *)
Implicit Types n : nat.

Lemma p (k : nat) : exists f : nat -> nat, f 1 = k.
Proof. eexists. exact eq_refl. Qed.
