(* Upstream writes this test with the [#[refine]] attribute on [Fixpoint],
   which Rocq 9.0.1 does not parse ("This command does not support this
   attribute: refine"). The tactic script below builds the same term. *)
Definition err : unit -> Set.
Proof.
  fix err 1.
  intro x.
  refine (let b := true in let f : unit -> unit -> unit := _ in unit).
  fix rec 2.
  exact (fun (arg : if b then unit else err tt) (y : unit) => tt).
Fail Defined.
Abort.
