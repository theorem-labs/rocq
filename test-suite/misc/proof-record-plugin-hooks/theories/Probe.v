(* misc/proof-record-plugin-hooks.sh compiles this file with -proof-record
   as it is, and once with the TestHookActivate and TestSetClosures lines
   commented out. Each of the first three proofs reaches one of the three
   choke points that ask the active hooks of a registry. *)

Declare ML Module "coq-test-suite.plugin_hooks".

TestHookActivate.

Class Pick (A : Type) := pick : A.
#[export] Instance pick_nat : Pick nat := 0.

(* A structure with NO canonical instance: a unification problem on its
   projection has no canonical solution, so the lookup falls through to the
   canonical-solution hooks. *)
Structure Wrap := wrap { unwrap : nat }.

(* [exists pick] runs typeclass resolution inside the proof, so it asks the
   active typeclass solvers. *)
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

(* A closure a plugin installs is process-wide state that no read sees: after
   it is installed, every proof of the process must store no term. *)
TestSetClosures.

Lemma after_closures : True.
Proof. exact I. Qed.
