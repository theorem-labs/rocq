(* Uses o through its statement only, which the kernel sees of an opaque
   constant: this proof replays although o's proof changed. *)
Require Import PR.A.
Lemma b : True. Proof. pose proof o. exact I. Qed.
