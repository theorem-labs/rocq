(* Gate review, INFRA-361 gap 2. No proof is open after the [Load], so
   stock rejects the [Proof.] below. Replay must report that error, and not
   the syntax error of the sentence after it. *)
Load "./Loaded.v".
Proof.
Definition broken := .
