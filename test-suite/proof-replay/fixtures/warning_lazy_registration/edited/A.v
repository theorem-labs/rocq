(* target names old, so stock creates the warning
   deprecated-reference-since-review84 then, the first time it is needed,
   and raises it (a plain warning). later's attribute names that warning,
   and an unknown warning is an error: stock accepts later only because
   target created it. A replay of target would not create it, so a proof
   that creates a warning, or raises one, is not replayed. Both trees are
   the same. *)
Set Warnings "+unknown-warning".

#[deprecated(since="review84")]
Definition old : True := I.

Lemma target : True.
Proof. exact old. Qed.

#[warnings="deprecated-reference-since-review84"]
Lemma later : True.
Proof. exact I. Qed.
