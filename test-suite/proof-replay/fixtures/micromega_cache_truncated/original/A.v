(* Delta review of e560ab16e4 (the reviewer's trigger). Both trees start
   with the same .lia.cache (tree_files), whose one entry is [target]'s
   problem with the result Certificate.Unknown. [warm] (under [Time], so it
   always runs) opens the table: the table keeps the entry's position, and
   lia reads the entry from the file only at a lookup that needs it. In the
   registration only, the Print before [target] writes the universe graph
   over .lia.cache, so [target]'s lia finds no entry there, computes a
   certificate and succeeds. The edited tree has no Print: stock reads
   Unknown and lia fails, so replay must fail too. What the table saw when
   it opened is the same in both trees. *)
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.
Set Warnings "-default-output-directory".

Lemma warm (x : Z) : 0 <= x -> 0 <= 2 * x.
Proof. intros. Time lia. Qed.

Print Universes Subgraph ( ) ".lia.cache".

Lemma target (x y : Z) : 3 * x + 5 * y = 7 -> x >= 0 -> y >= 0 -> x <= 3.
Proof. intros. lia. Qed.
