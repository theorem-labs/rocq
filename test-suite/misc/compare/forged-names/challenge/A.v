(* A name that the verdict file must escape. coqc cannot write a kernel
   name holding a line break -- only a crafted .vo can, and the checker's
   name check (checker/checkNames.mli) refuses one whose axiom line it
   would print -- so what is exercised here is the writer: a name that is
   not plain ASCII is escaped, the file stays valid JSON, and it holds
   exactly the records the same answer gives without that name. *)

Definition deux : nat := 2.

Definition théorème_ÿ : nat := deux.

Theorem thm : théorème_ÿ = 2.
Proof.
Admitted.
