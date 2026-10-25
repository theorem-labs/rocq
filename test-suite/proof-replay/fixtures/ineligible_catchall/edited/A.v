(* The `catchall` reason fires when one of the five instrumented handlers
   catches a critical exception (pretyping/evarconv.ml:282,285,1022,
   pretyping/evarsolve.ml:1786, tactics/equality.ml:466).  This proof drives
   canonical-structure resolution, which is the code under
   evarconv.ml:1022.  No input is known that makes that handler catch a
   critical exception, so the fixture carries `trigger_optional`: it compiles,
   and the runner prints SKIP while the record stays empty. *)
Structure carrier := Pack { sort : Type }.
Canonical Structure nat_carrier := Pack nat.
Canonical Structure prod_carrier (a b : carrier) := Pack (sort a * sort b)%type.

Definition pad := 1.

Lemma catchall_proof : True.
Proof.
  try (let _ := constr:(fun x : sort _ => x : (nat * nat)%type) in idtac).
  exact I.
Qed.
