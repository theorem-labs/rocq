(* Each proof reads one channel the recorder's fix round (9.2/proof-replay
   a1210789cf..23b37e36fb) added or changed: fresh's keyword test, a rewrite
   base found and one absent, the active typeclass solvers and the active
   coercion hooks. Nothing they read changes in the edited tree, so each
   must replay; a channel with no evaluator would make its proof miss. No
   numerals: their channel (prim_token) has its own fixture, eval_prim_token.
   The canonical-solution hooks are not here: a proof reaches them only after
   a canonical_structure lookup, a channel replay does not evaluate yet, so
   such a proof misses there whatever its hook read says. *)

Ltac t := let x := ident:(foo) in first [ clear x; exact true | exact false ].

Lemma lfresh : nat -> bool.
Proof. let H := fresh "foo" in intro H. t. Qed.

Parameter f g : nat -> nat.
Axiom fg : forall n, f n = g n.

Create Rewrite HintDb db.
#[export] Hint Rewrite fg : db.

Lemma lauto : forall n, f n = g n.
Proof. intro n. autorewrite with db. reflexivity. Qed.

Lemma labsent : bool.
Proof. tryif autorewrite with nodb then exact true else exact false. Qed.

Class Pick (A : Type) := pick : A.
#[export] Instance pick_bool : Pick bool := true.

Lemma uses_solver : exists b : bool, b = true.
Proof. exists pick. reflexivity. Qed.

(* A cast of a bare constant: an application under an expected type would
   also read its bidirectionality hint, a channel replay does not evaluate
   yet, and the proof would miss there before its hook read is checked. *)
Lemma uses_coercion : True.
Proof. try exact (tt : nat). exact I. Qed.

(* The edit: one definition that no proof reads, after every proof. *)
Definition pad := true.
