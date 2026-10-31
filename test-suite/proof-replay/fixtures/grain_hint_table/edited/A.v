Create HintDb db.

Lemma main_hint : True.
Proof. exact I. Qed.

(* The edit adds one entry to the database and changes nothing else.  `conj`
   is the constructor of `and`, so it can never close `True` and `reads_db`
   never uses it, but the whole-database digest changes.  It is a constant
   that already exists and it lives in Prop, so the edit adds no proof and
   makes no universe level: the universe counter at `reads_db`'s start is the
   registration's, and the database's grain is the only thing under test. *)
#[local] Hint Resolve main_hint conj : db.

Lemma reads_db : True.
Proof. auto with db. Qed.
