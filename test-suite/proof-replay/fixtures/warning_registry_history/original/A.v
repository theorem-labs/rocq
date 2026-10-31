(* Deprecation warnings are disabled. warm names old first, so warm creates
   the warning deprecated-reference-since-review84; target names old again
   and finds that warning created. later's attribute names the warning, and
   an unknown warning is an error. The edited tree no longer names old in
   warm, so stock creates the warning in target instead, and accepts later.
   target replayed would create nothing, so its start must see that the
   registry differs. *)
Set Warnings "-deprecated,+unknown-warning".

#[deprecated(since="review84")]
Definition old : True := I.

Lemma warm : True.
Proof. exact old. Qed.

Lemma target : True.
Proof. exact old. Qed.

#[warnings="deprecated-reference-since-review84"]
Lemma later : True.
Proof. exact I. Qed.
