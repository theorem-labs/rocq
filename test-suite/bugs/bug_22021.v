#[refine]
Fixpoint err (x : unit) :=
  let b := true in
  let f : unit -> unit -> unit := _ in
  unit.
Proof.
  fix rec 2.
  exact (fun (arg : if b then unit else err tt) (y : unit) => tt).
Fail Defined.
Abort.
