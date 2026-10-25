(* A closed proof of False accepted by the first version of the matching-term
   commit on this branch, 1f0e2ddc9518, and refused by every released
   toolchain. Found by the review of that commit (binary-equivalence-taiga,
   dispatch://BET-214, 2026-10-25).

   That commit gave the analysis and the rewriting the same stripped bodies,
   but started the rewriting at de Bruijn depth 0 while the analysis starts
   at the body's own recindx+1 abstractions. The test that recognises a
   reference to one of the mutual fixpoints then selected the innermost
   stripped binders instead: here, with a two-body inner block and the prefix
   [a h m], it matched [h] and [m]. Every application headed by [h] lost its
   leading arguments before the guard condition saw the body, so the
   non-decreasing call of the outer fixpoint placed in one of them was
   deleted and never checked, while the real recursive calls were not
   rewritten at all.

   The depth is now taken from the same recindx the analysis uses. *)

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

