(* -*- coq-prog-args: ("-native-compiler" "no") -*- *)
(* The binder of the recursive argument sits under a let and a let-pattern
   (a one-branch match on a pair): the shape Equations generates for a
   function on a nested inductive, here minimised from the obligation of
   [strip] in MetaRocq erasure ERemoveParams.v:552. The pair comes from a
   definition applied to the fixpoint, so delta, beta and iota bring the
   abstractions out, and the reduction drops nothing that mentions the
   fixpoint. Stock 9.2.0 accepts all three; the raw-prefix rule refused them
   with "Not enough abstractions in the definition" until it learnt to take
   those head-reduction steps. Native compilation is off because the native
   compiler cannot compile a fixpoint body with fewer syntactic abstractions
   than its recursive argument (rocq-prover/rocq#16599). *)

Inductive tree : Set := node : list tree -> tree.

(* [H] is a local definition of the context, as in the Equations term. *)
Definition size_local : tree -> nat.
Proof.
  pose (H := fun h : tree -> nat =>
    (fix go (l : list tree) : nat :=
       match l with nil => 0 | cons t l' => h t + go l' end, tt)).
  fix f 1.
  exact (let H := H f in
         let (s, p) := H in
         (fun (s0 : list tree -> nat) (_ : unit) (t : tree) =>
            match t with
            | node nil => O
            | node (cons t' l') => S (f t' + s0 l')
            end) s p).
Defined.

Print Assumptions size_local.
Example size_local_computes :
  size_local (node (cons (node nil) (cons (node nil) nil))) = 1 := eq_refl.

(* [H] is a global constant. *)
Definition H (h : tree -> nat) : (list tree -> nat) * unit :=
  (fix go (l : list tree) : nat :=
     match l with nil => 0 | cons t l' => h t + go l' end, tt).

Definition size_global : tree -> nat.
Proof.
  fix f 1.
  exact (let (s, p) := H f in
         (fun (s0 : list tree -> nat) (_ : unit) (t : tree) =>
            match t with
            | node nil => O
            | node (cons t' l') => S (f t' + s0 l')
            end) s p).
Defined.

Print Assumptions size_global.
Example size_global_computes :
  size_global (node (cons (node nil) (cons (node nil) nil))) = 1 := eq_refl.

(* The full shape: two arguments, the recursive one second; a nested pair of
   fixpoints over the nested lists; a let of it; a let-pattern on it; a
   beta redex; a second let-pattern under the beta binder; a second beta
   redex; then the two abstractions. Release-7 18da2c8ff497 refuses it with
   "expected at least 2 according to the "struct" annotation", as it refuses
   the MetaRocq definition. *)
Inductive term : Set :=
| tLeaf : term
| tNode : list term -> list (nat * term) -> term.

Definition strip : nat -> term -> nat.
Proof.
  pose (H := fun h : nat -> term -> nat =>
    ((fix strip_args (l : list term) : nat :=
        match l with nil => 0 | cons t l' => h 0 t + strip_args l' end),
     ((fix strip_brs (l : list (nat * term)) : nat :=
         match l with
         | nil => 0
         | cons p l' => match p with (n, t) => h n t + strip_brs l' end
         end), tt))).
  fix fix_0 2.
  exact (let H := H fix_0 in
         let (s, p) := H in
         (fun (s0 : list term -> nat) (p0 : (list (nat * term) -> nat) * unit) =>
            let (s1, s2) := p0 in
            (fun (s3 : list (nat * term) -> nat) (_ : unit) (app : nat) (t : term) =>
               match t with
               | tLeaf => app
               | tNode nil brs => S (s3 brs)
               | tNode (cons a args) brs => S (fix_0 app a + s0 args + s3 brs)
               end) s1 s2) s p).
Defined.

Print Assumptions strip.
Example strip_computes :
  strip 7 (tNode (cons tLeaf nil) (cons (5, tLeaf) nil)) = 13 := eq_refl.
