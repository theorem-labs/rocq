(* -*- coq-prog-args: ("-native-compiler" "no") -*- *)
(* The raw-prefix rule reduces the head of a fixpoint body to find its
   abstractions, as [whd_all] does, and like it reduces a value shared by
   several reads only once. Both bodies here read one value twice at each of
   N levels, so a walk that reduced it again at each read took 2^N
   reductions: on [top_const] (N = 28) 184 s and 27.7 GB, on [top_dup]
   (N = 32) more than the 8 GB it was given. Stock 9.2.0 checks both at
   once, and so does the walk, which shares each head normal form. *)
(* Expected time < 2.00s *)

Definition step (p : unit) : unit := match p with tt => match p with tt => tt end end.
Definition sel (u : unit) (h : nat -> nat) : nat -> nat := match u with tt => h end.
Definition u0 : unit := tt.
Definition u1 : unit := step u0.
Definition u2 : unit := step u1.
Definition u3 : unit := step u2.
Definition u4 : unit := step u3.
Definition u5 : unit := step u4.
Definition u6 : unit := step u5.
Definition u7 : unit := step u6.
Definition u8 : unit := step u7.
Definition u9 : unit := step u8.
Definition u10 : unit := step u9.
Definition u11 : unit := step u10.
Definition u12 : unit := step u11.
Definition u13 : unit := step u12.
Definition u14 : unit := step u13.
Definition u15 : unit := step u14.
Definition u16 : unit := step u15.
Definition u17 : unit := step u16.
Definition u18 : unit := step u17.
Definition u19 : unit := step u18.
Definition u20 : unit := step u19.
Definition u21 : unit := step u20.
Definition u22 : unit := step u21.
Definition u23 : unit := step u22.
Definition u24 : unit := step u23.
Definition u25 : unit := step u24.
Definition u26 : unit := step u25.
Definition u27 : unit := step u26.
Definition u28 : unit := step u27.
Definition top_const : nat -> nat.
Proof.
  fix f 1.
  refine (sel u28 (fun n : nat => match n with O => O | S p => f p end)).
Time Defined.

Definition dup (p : bool * bool) : bool * bool :=
  match p with (a, _) => match p with (_, b) => (a, b) end end.
Definition top_dup : nat -> nat.
Proof.
  fix f 1.
  refine (match dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup (dup ((true, true))))))))))))))))))))))))))))))))) with
          | (true, _) => (fun n : nat => match n with O => O | S p => f p end)
          | (false, _) => (fun _ : nat => O) end).
Time Defined.
