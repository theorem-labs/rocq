(* `Proof_record.digest_value` refuses a closure, an unforced lazy value, an
   object, an abstract block, a cycle, a custom block it cannot marshal, and a
   value of more than 2^25 distinct blocks (`lib/proof_record.ml:636-702`).
   Every value the recorder's choke points digest is kernel data or a glob AST
   — constant bodies (`kernel/environ.ml:253,289`), hint-database summaries of
   names and modes (`tactics/hints.ml:641-657,906`), Ltac and Ltac2 ASTs
   (`plugins/ltac/tacenv.ml:150-156`, `plugins/ltac2/tac2env.ml:85-90`),
   notations, implicit arguments, canonical structures, coercion and ring
   tables — so none of the first six is reachable from source.  The block count
   is: a constant whose body has more than 33,554,432 distinct blocks, read by
   a proof.

   The tree below has 2^22 leaves.  Its leaves carry distinct primitive
   The tree below has 2^21 leaves.  Its leaves carry distinct primitive
   integers because the kernel hash-conses a constant's body, and equal
   subtrees would collapse into one block and never reach the limit.
   `unhashable_proof` reads `big`, the recorder digests `big`'s body, and the
   walk passes the limit.  Measured on speed-r1, 2026-10-25, against a build
   of 588a2ebc: depth 20 stays under the limit (182 s, 2.6 GB, no reason
   recorded), depth 21 is the first that passes it (248 s, 4.7 GB) and depth
   22 also passes it (289 s, 7.5 GB, a 124 MB object).  Depth 21 is why this
   fixture is `slow`: its three compiles cost about 13 minutes. *)

From Corelib Require Import PrimInt63.

Inductive tree := L (k : int) | N (a b : tree).

Fixpoint build (d : nat) (k : int) : tree :=
  match d with
  | O => L k
  | S m => N (build m (PrimInt63.add k k)) (build m (PrimInt63.add (PrimInt63.add k k) (1%uint63)))
  end.

Definition big := Eval vm_compute in build 21 (1%uint63).

Definition pad := 0.

Lemma control : True.
Proof. exact I. Qed.

Lemma unhashable_proof : big = big.
Proof. reflexivity. Qed.
