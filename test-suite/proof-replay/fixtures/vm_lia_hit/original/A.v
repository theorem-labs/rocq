(* lia checks its certificate with a cast that the bytecode machine checks
   while the proof runs (ZTautoChecker ... <: ...), so its proof records the
   machine's view of the whole checker. The edited tree adds an unrelated
   definition; nothing the proofs read changes, so both replay. The second
   proof finds the checker in the machine's cache. *)
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma first (x y : Z) : x <= y -> x < y + 1.
Proof. lia. Qed.

Lemma second (x : Z) : 0 <= x -> 0 <= 2 * x.
Proof. lia. Qed.
