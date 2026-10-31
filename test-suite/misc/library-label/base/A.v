(* One object of each of the ten kinds the library label strips locations
   from (CONSTANT, INDUCTIVE, ABBREVIATION, NOTATION, TAC-DEFINITION,
   TAC-REDEFINITION, TacticGrammar and TacticSyntax, AUTOHINT with a Hint
   Extern, TAC2-DEFINITION), a few it reads as they are (a canonical
   structure among them), a functor, and the parts of the library's summary:
   an attribute of the library and a dependency, required at the end. Each
   variant of misc/library-label.sh changes one thing. *)

Attributes warn(note="label fixture", cats="label-fixture").

Inductive t := C1 | C2.

Definition f (n : nat) := S n.

Lemma l1 : forall n, f n = S n.
Proof. intros n. reflexivity. Qed.

Notation "x +++ y" := (Nat.add x y) (at level 50, left associativity).

Notation h := (f 0).

Ltac my_tac := intros; reflexivity.

Ltac my_tac2 := idtac.

Ltac my_tac2 ::= intros.

Tactic Notation "my_exact" constr(x) := exact x.

#[global] Hint Resolve l1 : core.

#[global] Hint Extern 1 (f _ = _) => my_tac : core.

#[global] Set Asymmetric Patterns.

Structure cs := { cs_car : Type; cs_op : cs_car -> cs_car }.
Definition cs_nat := {| cs_car := nat; cs_op := S |}.
Definition cs_nat2 := {| cs_car := nat; cs_op := pred |}.
Canonical Structure cs_nat.

Module Type S. Parameter u : Type. End S.

(* fc, tc and sc are Admitted on the line that declares them, so the axqed
   and axdef variants (which edit lines that hold only "Admitted.") leave
   them; the ftorqed, mtqed and sealqed variants make them Qed. sc is in the
   implementation of the sealed module M, whose signature declares it as a
   parameter. *)
Module F (X : S). Definition d := X.u. Lemma fc : True. Admitted. End F.

Module Type T. Lemma tc : True. Admitted. End T.

Module Type T2. Parameter sc : True. End T2.
Module M : T2. Lemma sc : True. Admitted. End M.

Definition g := f.

From Ltac2 Require Import Ltac2.

Ltac2 l2 (n : int) := n.

Require Corelib.Classes.CMorphisms.

(* An Admitted axiom (lax) and a section lemma (lsec): the S1b variants edit
   these. lax Admitted->Qed and l1 Qed->Admitted keep the label (version 3
   blinds the axiom-or-opaque distinction); lax Admitted->Defined and a
   Proof-using change on lsec move it. *)
Lemma lax : True.
Admitted.

Section Sec.
  Context (sv sw : nat).
  Lemma lsec : sv = sv. Proof using sv. reflexivity. Qed.
End Sec.

(* A structurally-decreasing fixpoint: the `guard` variant recompiles it with
   Unset Guard Checking, which changes its const_typing_flags (check_guarded) with
   body, type and universes unchanged, so the label must move (ROCQ: an unsound
   toolchain flag must not be kept over). The `addcon` variant adds a constructor
   to t above. *)
Fixpoint fg (n : nat) : nat := match n with O => O | S m => fg m end.
