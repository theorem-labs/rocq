(* lia looks its problem up in .lia.cache before it runs its prover. The
   registration tree has no cache, so lia computes the certificate and writes
   the cache. The edited tree is the same source beside a .lia.cache whose one
   entry is the registration's entry for this problem with its result changed
   to Certificate.Unknown (tree_files; make_cache.ml wrote it). Stock reads
   Unknown and lia fails, so replay must fail too. *)
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma target (x y : Z) : 3 * x + 5 * y = 7 -> x >= 0 -> y >= 0 -> x <= 3.
Proof. intros. lia. Qed.
