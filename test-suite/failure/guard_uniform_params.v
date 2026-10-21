(* The guard checker must refuse an inner fixpoint whose "uniform" argument is
   only justified by the recursive calls that are written out in full. An
   occurrence of the inner fixpoint that is passed on without being applied
   imposes no constraint on the analysis, so the subterm information of the
   first argument ever passed to that parameter was assumed to hold for every
   later call, and a non-decreasing outer recursive call went through.

   The three definitions below are the three known counterexamples: the first
   was produced by a model under evaluation (binary-equivalence-taiga,
   dispatch://BET-214), the second and third are the counterexamples of
   rocq-prover/rocq#21797 and rocq-prover/rocq#22382. Each of them yields a
   closed proof of False that uses no axiom and no typing flag. *)

(* An unapplied occurrence of the inner fixpoint g, hidden in a function
   position, makes g's parameter u look uniform. *)
Inductive T : Set := C : T -> T | L : T.
Definition P (t : T) : Type := match t with L => unit | C _ => False end.
Definition R (u : T) (k : nat) : Type := match k with O => P u | S _ => False end.
Fail Fixpoint f (t : T) : P t :=
  match t as t0 return P t0 with
  | L => tt
  | C t' =>
      (fix g (u : T) (k : nat) {struct k} : R u k :=
         match k as k0 return R u k0 with
         | O => f u
         | S k' =>
             match k' as k0 return (R (C t') k0 -> False) with
             | O => fun x => x
             | S _ => fun x => x
             end ((fun h : forall (u : T) (k : nat), R u k => h (C t') k') g)
         end) t' (S O)
  end.

(* rocq-prover/rocq#21797: the arguments of a recursive call were not analysed,
   so a recursive call inside an argument imposed no constraint. *)
Fail Fixpoint F2 (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    (fix G (a : nat) (f : nat -> nat -> nat) (m : nat) {struct m} : nat :=
      match m with
      | 0 => S (F2 a)
      | S m' => f (G n f m') m'
      end) n' (fun x _ => x) n'
  end.

(* rocq-prover/rocq#22382: a local definition in the prefix of the inner
   fixpoint was counted as a formal argument, so the uniform arguments were
   counted at the wrong positions. *)
Definition relay (outer : nat -> Type) (seed : nat) : nat -> nat -> Type :=
  fix inner (carry : nat := seed) (p m : nat) {struct m} : Type :=
    match m with
    | O => outer p -> False
    | S rest => inner carry rest
    end.
Fail Fixpoint russell (n : nat) : Type :=
  match n with
  | O => True
  | S smaller => relay russell n smaller smaller
  end.
