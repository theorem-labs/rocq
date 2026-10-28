(* The source-duplicating dead branch of guard_cofix_dead_dup_source.v, with
   each copy wrapping the substituted variable in a 300-node chain, so the
   two copies of a level share no node and a comparison stopped at a fixed
   size would call them unequal and re-examine every copy. The memo of the
   cofixpoint guard's dropped-material walk compares with a budget shared by
   the whole walk rather than a per-comparison cap, so no single comparison
   is cut off here and this stays linear in the depth: a fixed 256-node cap
   took 97 s on this file. Valid; stock Rocq 9.2.0 checks it in about 65 ms. *)
(* Expected time < 2.00s *)
CoInductive St : Type := c : St -> St.
Inductive Two : Type := two : St -> St -> Two.
Definition W := Eval cbv in fun s : St => Nat.iter 300 c s.
Definition D (f : St -> St) : St -> St :=
  Eval cbv delta [W] beta in
  fun s => match two (f (W s)) (f (W s)) with two a b => c a end.
Definition q0 : St -> St := fun s => s.
Definition q1 : St -> St := D q0.
Definition q2 : St -> St := D q1.
Definition q3 : St -> St := D q2.
Definition q4 : St -> St := D q3.
Definition q5 : St -> St := D q4.
Definition q6 : St -> St := D q5.
Definition q7 : St -> St := D q6.
Definition q8 : St -> St := D q7.
Time CoFixpoint r : St := match false with true => q8 r | false => c r end.
