(* Each proof's [Proof using] sentence gives a set of section variables,
   which the proof records (proof_using_set). [same] declares the variables of
   its statement (none), and nothing that set depends on changes, so [same]
   must replay. [changed] declares All; the edited tree declares one more
   section variable before it, so its set changes. The set is computed from
   the section context, which the proof records at its start, so [changed]
   misses there, on named_context. Neither sentence names a collection. *)
Section S.
Variable n : nat.

Lemma same : True.
Proof using Type. exact I. Qed.
Variable m : nat.
Lemma changed : True.
Proof using All. exact I. Qed.
End S.
