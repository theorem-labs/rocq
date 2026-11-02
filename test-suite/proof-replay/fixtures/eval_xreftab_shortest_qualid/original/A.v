(* Each proof prints a constant, named by its absolute name, and the
   printer asks the global nametab for the constant's shortest name (a
   reverse lookup). The edited tree imports a module M that defines another
   c before the proofs: PR.A.c keeps its kernel name and its absolute name,
   and its shortest name becomes A.c. [changed] prints PR.A.c and must miss
   on the xreftab/shortest_qualid read. [same] prints PR.A.d, whose shortest
   name stays d, and must replay. *)
Definition c := O.
Definition d := O.

Lemma same : True.
Proof. let x := constr:(PR.A.d) in idtac x. exact I. Qed.

Lemma changed : True.
Proof. let x := constr:(PR.A.c) in idtac x. exact I. Qed.
