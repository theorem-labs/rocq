(* The [in] clause matches the index of [t] against [true], a pattern that is
   not a variable, so the return clause binds that index under a generated
   name. The arity of T gives the index no name, so it takes the name that
   Implicit Types reserves for bool, read from the reverse reserved-type
   table: b here, c in the edited tree. The proof term holds that name, so the
   stock object differs from the registered one, and replay must give the
   stock object (gate review of 079bc4cb71, CF6). *)
Inductive T : bool -> Type := T0 : T true.

Implicit Types b : bool.

Lemma q (t : T true) : True.
Proof. exact (match t in T true return True with T0 => I end). Qed.
