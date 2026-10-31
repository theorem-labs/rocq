(* A universe-polymorphic instance's declaration makes levels: the hint
   the instance declares takes a fresh instance of it
   (Classes.instance_hook -> Hints.add_resolves -> UnivGen.fresh_level),
   and the hint keeps those levels in the library. Stock names them from the
   counters at the closer, which the instance's own tactics moved ([pose]
   makes a level). The proof after each instance makes levels of its own,
   so it names them as stock does only if the counters stand where stock
   leaves them, and the hint at the end takes a hint key. *)

#[universes(polymorphic)] Class C (A : Type) := c : A -> A.

#[universes(polymorphic)] Instance inst (A : Type) : C A.
Proof. pose (T := Type). exact (fun x => x). Qed.

Lemma later : forall A : Type, A -> option A.
Proof. intros A x. exact (Some x). Qed.

(* The same with a sort quality: the hint's fresh instance makes a sort
   variable too. *)
#[universes(polymorphic)] Class CS@{s ; u |} (A : Type@{s ; u}) := cs : A -> A.

#[universes(polymorphic)] Instance instS@{s ; u |} (A : Type@{s ; u}) : CS@{s ; u} A.
Proof. exact (fun x => x). Qed.

Lemma last : forall A : Type, A -> option A.
Proof. intros A x. exact (Some x). Qed.

#[export] Hint Resolve later : core.
