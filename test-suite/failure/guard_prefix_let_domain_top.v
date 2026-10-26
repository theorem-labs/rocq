(* breaka/D5.v through a let: the block's function reaches a binder's DOMAIN only after the let is substituted. Rocq 9.0.1 and the release-7 rule raise Anomaly "in check_one_fix: Bad occurrence of recursive call."; it must be a guard refusal. dispatch://BET-214 *)
(* breaka/D5 through a let: the block's function reaches a prefix binder's
   DOMAIN only after zeta. raw_prefix_escapes sees "Rel 1" (the let) in
   the domain; check_occur in inductive_of_mutfix then sees the function
   itself and raises "Bad occurrence of recursive call". *)
Definition top_dom : nat -> nat.
Proof.
  fix f 1.
  refine (let x := f in _).
  refine (fun (n : (fun _ : nat -> nat => nat) x) => _).
  exact O.
Fail Defined.
Abort.
