(* A file the answer adds. The challenge does not hold it, so nothing in it
   is compared; the kernel still checks it. *)

Require Import A.

Definition twice (t : tree) : tree := mirror (mirror t).

Lemma twice_id : forall t : tree, twice t = t.
Proof. exact thm. Qed.
