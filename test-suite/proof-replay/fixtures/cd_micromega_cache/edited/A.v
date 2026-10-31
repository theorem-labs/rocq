(* Gate review of 26528c8a34, finding CF4-R2 (the reviewer's trigger).
   [warm] opens the lia cache in cache0/: the table is the one of
   cache0/.lia.cache, whose one entry is the genuine entry for [target]'s
   problem. [Time] keeps [warm] from replaying. After [Cd ".."], lia reads
   that entry again from .lia.cache in this directory (tree_files): the
   registration's holds the genuine entry, the edited tree's holds the same
   key with the result Certificate.Unknown. Stock reads Unknown and lia
   fails. The micromega_cache read of [target] is the digest of
   cache0/.lia.cache when it opened, the same in both trees, so without the
   cd fence [target] replays. *)
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.
Set Warnings "-change-dir-deprecated".

Cd "cache0".

Lemma warm (x : Z) : 0 <= x -> 0 <= 2 * x.
Proof. intros. Time lia. Qed.

Cd "..".

Lemma target (x y : Z) : 3 * x + 5 * y = 7 -> x >= 0 -> y >= 0 -> x <= 3.
Proof. intros. lia. Qed.
