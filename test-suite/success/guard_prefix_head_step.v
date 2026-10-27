(* -*- coq-prog-args: ("-native-compiler" "no") -*- *)
(* Terminating fixpoints whose abstractions appear only after a
   head-reduction step that the raw-prefix rule takes (delta, iota of a
   match or of a projection on a constructor, a read of a bound variable at
   the head), and whose steps drop nothing that mentions the fixpoint. Stock
   9.2.0 accepts each of them; release-8 a3a27a829aa2 refuses each with "Not
   enough abstractions in the definition", and so does release-7
   18da2c8ff497 except [top_pattern] (its walk does not follow the let to
   the match). The first eight are the bodies of
   failure/guard_prefix_head_step_drops.v with the dropped call replaced by
   [O], so that the refusals there come from the call. Native compilation is
   off because the native compiler cannot compile such a body
   (rocq-prover/rocq#16599). *)

Definition drop (a : nat) (g : nat -> nat) : nat -> nat := g.
Definition top_drop_const : nat -> nat.
Proof.
  fix f 1.
  refine (drop O _).
  intro n. destruct n as [|p].
  - exact O.
  - exact (f p).
Defined.

Definition top_drop_field : nat -> nat.
Proof.
  fix f 1.
  refine (let (_, g) := (O, fun n : nat => match n with O => O | S p => f p end) in g).
Defined.

Definition top_pattern : nat -> nat.
Proof.
  pose (H := fun h : nat -> nat =>
    (fun n : nat => match n with O => O | S p => h p end, O)).
  fix f 1.
  refine (let H := H f in let (s, p) := H in (fun (s0 : nat -> nat) (_ : nat) => s0) s p).
Defined.

Definition top_scrut_beta : nat -> nat.
Proof.
  fix f 1.
  refine (match (fun _ : nat => (fun n : nat => match n with O => O | S p => f p end, tt)) O with
          | (g, _) => g end).
Defined.

Definition top_selected : nat -> nat.
Proof.
  pose (sel := fun (h : nat -> nat) (b : bool) =>
    if b then (fun n : nat => match n with O => O | S p => h p end) else (fun _ : nat => O)).
  fix f 1.
  refine (sel f true).
Defined.

Definition K (n : nat) : Type := nat -> nat.
Definition top_ctor_param : nat -> nat.
Proof.
  fix f 1.
  refine (let (g, _) := @pair (K O) unit
                          (fun n : nat => match n with O => O | S p => f p end) tt in g).
Defined.

Set Primitive Projections.
Record R := mkR { r1 : nat; r2 : nat -> nat }.
Unset Primitive Projections.
Definition top_proj_field : nat -> nat.
Proof.
  fix f 1.
  refine ((mkR O (fun n : nat => match n with O => O | S p => f p end)).(r2)).
Defined.

Definition top_return_pred : nat -> nat.
Proof.
  fix f 1.
  refine (match tt return K O with
          | tt => fun n : nat => match n with O => O | S p => f p end end).
Defined.

(* a projection of a record that is not primitive (a match) *)
Record P := mkP { p1 : nat -> nat; p2 : unit }.
Definition HP (h : nat -> nat) : P := mkP (fun n : nat => match n with O => O | S p => h p end) tt.
Definition top_nonprim_proj : nat -> nat.
Proof. fix f 1. exact (p1 (HP f)). Defined.

(* a constructor with a let-in argument, read by the branch *)
Inductive T : Type := mk (a : nat) (b := a) (g : nat -> nat).
Definition HT (h : nat -> nat) : T := mk O (fun n : nat => match n with O => O | S p => h p end).
Definition top_ctor_letin : nat -> nat.
Proof. fix f 1. exact (match HT f with mk a g => g end). Defined.

(* iota selecting the second constructor, of [bool], [nat] and [sum] *)
Definition top_select_false : nat -> nat.
Proof.
  fix f 1.
  refine (if false then (fun _ : nat => O) else (fun n : nat => match n with O => O | S p => f p end)).
Defined.

Definition top_select_S : nat -> nat.
Proof.
  fix f 1.
  refine (match S O with
          | O => (fun _ : nat => O)
          | S q => (fun n : nat => match n with O => O | S p => f p end) end).
Defined.

Definition top_select_inr : nat -> nat.
Proof.
  fix f 1.
  refine (match @inr nat unit tt with
          | inl _ => (fun _ : nat => O)
          | inr _ => (fun n : nat => match n with O => O | S p => f p end) end).
Defined.

(* a match applied to an argument that its branch reads *)
Definition top_match_applied : nat -> nat.
Proof.
  fix f 1.
  refine ((match tt return (nat -> nat) -> nat -> nat with tt => fun (g : nat -> nat) => g end)
            (fun n : nat => match n with O => O | S p => f p end)).
Defined.

(* an inductive with a let-in parameter *)
Inductive W (A : Type) (B := A) : Type := mkW (x : B) (h : nat -> nat).
Definition top_letin_param : nat -> nat.
Proof.
  fix f 1.
  refine (match mkW nat O (fun n : nat => match n with O => O | S p => f p end) with
          | mkW _ x h => h end).
Defined.

(* a primitive record with a let field *)
Set Primitive Projections.
Record R3 := mkR3 { a3 : nat; b3 := a3; c3 : nat -> nat }.
Unset Primitive Projections.
Definition top_prim_letfield : nat -> nat.
Proof.
  fix f 1.
  refine ((mkR3 O (fun n : nat => match n with O => O | S p => f p end)).(c3)).
Defined.

(* a nested fixpoint whose abstraction appears after delta of [id], and
   whose body calls the enclosing function on a subterm *)
Definition outer_inner_id : nat -> nat.
Proof.
  fix outer 1. intro n. destruct n as [|m].
  - exact O.
  - refine ((_ : nat -> nat) m). fix inner 1. refine (id _).
    intro k. destruct k as [|j].
    + exact (outer m).
    + exact (inner j).
Defined.

(* The shape of [ok] in bug_22645.v (rocq-prover/rocq#22645) with a helper
   that reads both of its function arguments, so that the steps drop no
   mention of [inner]: delta of a local definition, delta of [ap_both],
   beta. (With [ap_real], which drops [inner a], the raw-prefix rule refuses
   [ok], because a dropped mention of the block is refused even when it is a
   partial application.) *)
Definition ap_both (g1 g2 cont : nat -> Type) (a : nat) : nat -> Type :=
  fun m => match m with O => cont a | S k => prod (g1 k) (g2 k) end.
Fixpoint ok (n : nat) : Type :=
  match n with
  | O => True
  | S p =>
      let actual := ap_both in
      (ltac:(fix inner 2; intros a;
             exact (actual (inner a) (inner (S a)) (fun _ => ok p) a))
        : nat -> nat -> Type) p p
  end.

(* The bodies of failure/guard_prefix_head_step_more_drops.v with [O] in
   place of the dropped call. [top_select_S], [top_select_false],
   [top_letin_param] and [top_prim_letfield] above are the controls of
   [top_select_S_dead], [top_unselected_first], [top_letin_param_dead] and
   [top_prim_letfield_dead]. *)
Definition top_ctor_letin_o : nat -> nat.
Proof.
  fix f 1.
  refine (match mk O (fun n : nat => match n with O => O | S p => f p end) with
          | mk a g => g end).
Defined.

Definition top_match_applied_o : nat -> nat.
Proof.
  fix f 1.
  refine ((match tt return nat -> nat -> nat with
           | tt => fun (x : nat) => fun n : nat => match n with O => O | S p => f p end end)
            O).
Defined.

Definition top_proj_via_let_o : nat -> nat.
Proof.
  fix f 1.
  refine (let r := mkR O (fun n : nat => match n with O => O | S p => f p end) in r.(r2)).
Defined.

Definition top_letpat_used_let_o : nat -> nat.
Proof.
  fix f 1.
  refine (let p := (O, fun n : nat => match n with O => O | S p => f p end) in
          let (a, h) := p in h).
Defined.

Definition top_inr_param_o : nat -> nat.
Proof.
  fix f 1.
  refine (match @inr (K O) unit tt with
          | inl _ => (fun _ : nat => O)
          | inr _ => (fun n : nat => match n with O => O | S p => f p end) end).
Defined.

Definition top_letin_app_o : nat -> nat.
Proof.
  fix f 1.
  refine ((let x := O in fun g : nat -> nat => g)
            (fun n : nat => match n with O => O | S p => f p end)).
Defined.

Definition outer_drop_o : nat -> nat.
Proof.
  fix outer 1. intro n. destruct n as [|m].
  - exact O.
  - refine ((_ : nat -> nat) m). fix inner 1.
    refine (drop O _).
    intro k. destruct k as [|j].
    + exact (outer m).
    + exact (inner j).
Defined.

Example computes :
  (top_drop_const 3, top_drop_field 3, top_pattern 3, top_scrut_beta 3, top_selected 3,
   top_ctor_param 3, top_proj_field 3, top_return_pred 3, top_nonprim_proj 3,
   top_ctor_letin 3, top_select_false 3, top_select_S 3, top_select_inr 3,
   top_match_applied 3, top_letin_param 3, top_prim_letfield 3, outer_inner_id 3)
  = (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0) := eq_refl.

Example computes_o :
  (top_ctor_letin_o 3, top_match_applied_o 3, top_proj_via_let_o 3, top_letpat_used_let_o 3,
   top_inr_param_o 3, top_letin_app_o 3, outer_drop_o 3)
  = (0, 0, 0, 0, 0, 0, 0) := eq_refl.
