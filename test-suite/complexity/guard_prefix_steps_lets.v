(* -*- coq-prog-args: ("-native-compiler" "no") -*- *)
(* The raw-prefix rule reduces the head of a fixpoint body to find its
   abstractions. Here the head is a match on a pair computed under 36
   doubling lets, whose last value is dropped by a beta redex: unfolded, it is
   a term of 2^36 leaves. A walk that substituted the lets took exponential
   time on it (918 s at n = 36); the walk binds them, and stock 9.2.0 checks
   the definition at once. *)
(* Expected time < 2.00s *)

Definition fstp (p : ((nat -> nat) * unit)%type) : nat -> nat := match p with (h, _) => h end.
Definition top : nat -> nat.
Proof.
  fix f 1.
  refine (fstp
  (let x0 := O in
   let x1 := Nat.add x0 x0 in
   let x2 := Nat.add x1 x1 in
   let x3 := Nat.add x2 x2 in
   let x4 := Nat.add x3 x3 in
   let x5 := Nat.add x4 x4 in
   let x6 := Nat.add x5 x5 in
   let x7 := Nat.add x6 x6 in
   let x8 := Nat.add x7 x7 in
   let x9 := Nat.add x8 x8 in
   let x10 := Nat.add x9 x9 in
   let x11 := Nat.add x10 x10 in
   let x12 := Nat.add x11 x11 in
   let x13 := Nat.add x12 x12 in
   let x14 := Nat.add x13 x13 in
   let x15 := Nat.add x14 x14 in
   let x16 := Nat.add x15 x15 in
   let x17 := Nat.add x16 x16 in
   let x18 := Nat.add x17 x17 in
   let x19 := Nat.add x18 x18 in
   let x20 := Nat.add x19 x19 in
   let x21 := Nat.add x20 x20 in
   let x22 := Nat.add x21 x21 in
   let x23 := Nat.add x22 x22 in
   let x24 := Nat.add x23 x23 in
   let x25 := Nat.add x24 x24 in
   let x26 := Nat.add x25 x25 in
   let x27 := Nat.add x26 x26 in
   let x28 := Nat.add x27 x27 in
   let x29 := Nat.add x28 x28 in
   let x30 := Nat.add x29 x29 in
   let x31 := Nat.add x30 x30 in
   let x32 := Nat.add x31 x31 in
   let x33 := Nat.add x32 x32 in
   let x34 := Nat.add x33 x33 in
   let x35 := Nat.add x34 x34 in
   let x36 := Nat.add x35 x35 in
   (fun _ : nat => (fun n : nat => match n with O => O | S p => f p end, tt)) x36)).
Time Defined.
