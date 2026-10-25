(* misc/proof-record-hook-override.sh compiles this file with -proof-record
   twice as it is, and once with the OVERRIDE line replaced by
   TestHookRegister. Each proof below reaches one of the three choke points
   that record the names of a registry of hooks. *)

Declare ML Module "coq-test-suite.hook_override".

TestHookActivate.

Class Pick (A : Type) := pick : A.
#[export] Instance pick_nat : Pick nat := 0.

(* A structure with NO canonical instance: a unification problem on its
   projection has no canonical solution, so the lookup falls through to the
   canonical-solution hooks. *)
Structure Wrap := wrap { unwrap : nat }.

(* OVERRIDE *)

(* [exists pick] runs typeclass resolution inside the proof, so the record of
   [uses_solver] holds the typeclass_solver read. *)
Lemma uses_solver : exists n : nat, n = 0.
Proof. exists pick. reflexivity. Qed.

(* [tt] is a [unit] where a [nat] is expected, and no coercion applies, so
   elaboration asks the coercion hooks. They return None, so the step fails
   and [try] keeps the proof alive. A [Fail] here would mark the proof
   ineligible with reason control_flag and hide the read. *)
Lemma uses_coercion : True.
Proof. try exact (S tt). exact I. Qed.

(* [unwrap ?w] against [0] holds an evar, so the unification runs under
   evarconv and asks for a canonical solution of [unwrap]. There is none, so
   the lookup falls through to the canonical-solution hooks. They return None,
   so the step fails and [try] keeps the proof alive. *)
Lemma uses_canonical : True.
Proof. try exact (eq_refl : unwrap _ = 0). exact I. Qed.
