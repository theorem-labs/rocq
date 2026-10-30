(* The control of warning_registry_history: warm still creates the disabled
   warning in the edited tree, which only adds an unrelated definition, so
   target starts with the same registry and replays, and so does later. *)
Set Warnings "-deprecated,+unknown-warning".

#[deprecated(since="review84")]
Definition old : True := I.

Definition unrelated : nat := 0.

Lemma warm : True.
Proof. exact old. Qed.

Lemma target : True.
Proof. exact old. Qed.

#[warnings="deprecated-reference-since-review84"]
Lemma later : True.
Proof. exact I. Qed.
