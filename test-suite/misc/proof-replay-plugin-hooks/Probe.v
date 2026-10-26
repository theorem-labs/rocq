(* misc/proof-replay-plugin-hooks.sh compiles this file in four variants,
   with the TestHookActivate and TestSetClosures lines each kept or commented
   out. The first three proofs each reach one of the three choke points that
   ask the active hooks of a registry; the last three ask none. No numerals:
   commenting a line out moves the text after it, and a numeral's recorded
   interpretation holds its source position. *)

Declare ML Module "coq-test-suite.plugin_hooks".

TestHookActivate.

Class Pick (A : Type) := pick : A.
#[export] Instance pick_bool : Pick bool := true.

(* A structure with NO canonical instance: a unification problem on its
   projection falls through to the canonical-solution hooks. *)
Structure Wrap := wrap { unwrap : bool }.

(* Typeclass resolution inside the proof asks the active solvers. *)
Lemma uses_solver : exists b : bool, b = true.
Proof. exists pick. reflexivity. Qed.

(* No coercion takes [tt] to a [nat], so elaboration asks the coercion
   hooks, which decline; [try] keeps the proof alive. A cast of a bare
   constant: an application under an expected type would also read its
   bidirectionality hint, a channel replay does not evaluate yet, and the
   proof would miss there before its hook read is checked. *)
Lemma uses_coercion : True.
Proof. try exact (tt : nat). exact I. Qed.

(* [unwrap ?w] against [true] asks for a canonical solution of [unwrap];
   there is none, so the lookup asks the canonical-solution hooks. The proof
   also reads the notation [=] and the canonical_structure table, channels
   replay does not evaluate yet, so it misses on one of them in every grade
   (the runs show notation): the test requires only that it never replays. *)
Lemma uses_canonical : True.
Proof. try exact (eq_refl : unwrap _ = true). exact I. Qed.

Lemma before_closures : True.
Proof. exact I. Qed.

(* A closure a plugin installs over Rocq's own is process-wide state that no
   read sees: from here on no proof of the process may be replayed. The
   closures are inert for [exact I] against [True]. *)
TestSetClosures.

Lemma after_closures : True.
Proof. exact I. Qed.

Lemma after_closures_2 : True.
Proof. exact I. Qed.
