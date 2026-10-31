(* The global graph does not check universes (Unset Universe Checking), and
   target turns checking on for itself (bypass_check(universes=no)). Its cast
   needs u <= v. The edited tree declares v < u instead, so stock rejects
   target. On the global graph every constraint holds, so an order computed
   there is the same in both trees: replay must not reuse target's term. *)
Universe u v.
Constraint u <= v.
Unset Universe Checking.

#[bypass_check(universes=no)]
Definition target : True.
Proof.
  let t := constr:(fun X : Type@{u} => (X : Type@{v})) in
  exact I.
Qed.
