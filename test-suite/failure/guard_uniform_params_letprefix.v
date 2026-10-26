(* A definition that this toolchain REFUSES ON PURPOSE, and that Rocq 9.2.0
   and 9.3+rc1 accept. It is here so that a reader of the suite can tell this
   deliberate refusal from a defect.

   [inner] opens with a local definition, [carry := smaller], before its two
   formal arguments. The old analysis counted that local definition as a formal
   argument, so it measured the uniform prefix at the wrong positions: it
   believed [p] stays fixed across the recursive calls of [inner] and carried
   the subterm information of the first value ever passed there into every
   later call. That is the hole of rocq-prover/rocq#22382, and it yields a
   closed proof of False with no axiom and no typing flag
   (test-suite/bugs/bug_22382.v). rocq-prover/rocq#22384 closes it by inlining
   local definitions before counting, which is why a definition of this shape
   is now refused even when it happens to terminate: the analysis can no longer
   tell that [p] is always [smaller], and refusing is the safe answer.

   The same refusal is given by upstream master and by Rocq 9.3.0, so a
   development that relies on this shape already fails on those toolchains
   (measured 2026-10-25, binary-equivalence-taiga, dispatch://BET-214). The
   remedy in a development is to write the carried value as an ordinary
   argument of the inner fixpoint instead of a local definition. *)

Fail Fixpoint total (n : nat) : nat :=
 match n with
 | O => O
 | S smaller =>
   (fix inner (carry : nat := smaller) (p m : nat) {struct m} : nat :=
     match m with O => total p | S rest => inner carry rest end) smaller smaller
 end.
