(* Gate review, INFRA-361 gap 2. A [Load] trips the process-wide fence.
   [before] opens before the [Load], a late command, and runs. [later] opens
   after it: the registration marks it ineligible (reason load), and it runs.
   The edited L.v changes only [unused], which no read of [later] sees, so
   without the fence [later] replays. *)
Lemma before : True.
Proof. exact I. Qed.

Load "./L.v".

Lemma later : 1 = 1.
Proof. reflexivity. Qed.
