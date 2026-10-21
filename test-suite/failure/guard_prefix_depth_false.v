(* A closed proof of False accepted by the matching-term candidate of this
   branch and refused by every released toolchain: the rewriting walked the
   stripped bodies at the wrong de Bruijn depth, so the test that recognises
   the block selected the innermost prefix binders and deleted arguments from
   an unrelated application. Found by the break attempt. dispatch://BET-214 *)

(* E1 — exploit of the de Bruijn shift in [drop_uniform_parameters].

   The candidate analyses the STRIPPED bodies with [aux (recindx+1)] but
   rewrites the same stripped bodies with [aux 0], so the test
   [n > k && n <= k + nbodies] no longer selects the mutual fixpoint
   variables: at depth [k] in a stripped body it selects the [nbodies]
   innermost binders of the stripped prefix.  With a two-body inner block and
   prefix [a h m] those are [m] (the structural argument) and [h].  Every
   application headed by [h] therefore loses its first [nuniformparams]
   arguments BEFORE the guard condition looks at the body.  Hide a
   non-decreasing call of the outer fixpoint there and nobody checks it. *)

Fail Fixpoint outer (n : nat) {struct n} : False :=
  (fix g0 (a : nat) (h : False -> False) (m : nat) {struct m} : False :=
     match m with
     | O => h (outer a)
     | S k => g0 a h k
     end
   with g1 (a : nat) (h : False -> False) (m : nat) {struct m} : False :=
     match m with
     | O => h (outer a)
     | S k => g1 a h k
     end
   for g0) n (fun x : False => x) O.

