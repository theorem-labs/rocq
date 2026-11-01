(* breaka/D5 through a let: the block's function reaches a prefix binder's
   DOMAIN only after zeta. On the release-7 cut 18da2c8ff497,
   raw_prefix_escapes sees "Rel 1" (the let) in the domain, and check_occur
   in inductive_of_mutfix then sees the function itself and raises Anomaly
   "in check_one_fix: Bad occurrence of recursive call." (Port90's
   bug-finder file a1). It must be a guard refusal. Ported from
   9.0/guard-cofix-prefix 9e24663c6e07. dispatch://BET-214 *)
Definition top_dom : nat -> nat.
Proof.
  fix f 1.
  refine (let x := f in _).
  refine (fun (n : (fun _ : nat -> nat => nat) x) => _).
  exact O.
Fail Defined.
Abort.
