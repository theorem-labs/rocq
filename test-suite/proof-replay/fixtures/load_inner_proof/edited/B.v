(* Gate review, INFRA-361 gap 2. [inner] now comes from the [Load], and its
   record is eligible. Replay must not take it as a candidate: no proof is
   open after the [Load], so stock rejects the [Proof.] below, and replay
   must report that error, and not the syntax error of the sentence after
   it. *)
Load "./Loaded.v".
Proof.
Definition broken := .
