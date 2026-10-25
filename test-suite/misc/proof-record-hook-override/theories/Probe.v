(* misc/proof-record-hook-override.sh compiles this file with -proof-record
   twice as it is, and once with the OVERRIDE line replaced by
   TestSolverRegister. *)

Declare ML Module "coq-test-suite.hook_override".

TestSolverActivate.

Class Pick (A : Type) := pick : A.
#[export] Instance pick_nat : Pick nat := 0.

(* OVERRIDE *)

(* [exists pick] runs typeclass resolution inside the proof, so the record of
   [uses_solver] holds the typeclass_solver read. *)
Lemma uses_solver : exists n : nat, n = 0.
Proof. exists pick. reflexivity. Qed.
