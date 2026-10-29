(* par: runs t in a tactic worker process, where no recorder runs, so the
   record of lpar would not hold the definition of t. The recorder marks such
   a proof ineligible (reason par), and replay must never use it: the edited
   tree defines t as exact false, so stock gives false where the
   registration's term is true. lall runs t in this process: its record holds
   t's definition, and it misses on that read. control hits. *)

Ltac t := exact true.

Lemma lpar : bool.
Proof. par: t. Qed.

Lemma lall : bool.
Proof. all: t. Qed.

Lemma control : True.
Proof. exact I. Qed.
