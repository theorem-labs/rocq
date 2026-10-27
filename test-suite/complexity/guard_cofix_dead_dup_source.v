(* A dead branch that duplicates its sub-term per level in the SOURCE
   ([two (f s) (f s)]), so the copies are not physically shared. The
   cofixpoint guard's dropped-material walk memoises checked sub-terms up to
   structural equality, so this is linear in the depth; a memo by physical
   identity is exponential (depth 16 did not finish in 150 s). Valid; stock
   Rocq 9.2.0 checks it in about 60 ms. *)
(* Expected time < 1.00s *)
CoInductive St : Type := c : St -> St.
Inductive Two : Type := two : St -> St -> Two.
Definition D (f : St -> St) : St -> St :=
  fun s => match two (f s) (f s) with two a b => c a end.
Definition q0 : St -> St := fun s => s.
Definition q1 : St -> St := D q0.
Definition q2 : St -> St := D q1.
Definition q3 : St -> St := D q2.
Definition q4 : St -> St := D q3.
Definition q5 : St -> St := D q4.
Definition q6 : St -> St := D q5.
Definition q7 : St -> St := D q6.
Definition q8 : St -> St := D q7.
Definition q9 : St -> St := D q8.
Definition q10 : St -> St := D q9.
Definition q11 : St -> St := D q10.
Definition q12 : St -> St := D q11.
Definition q13 : St -> St := D q12.
Definition q14 : St -> St := D q13.
Definition q15 : St -> St := D q14.
Definition q16 : St -> St := D q15.
Definition q17 : St -> St := D q16.
Definition q18 : St -> St := D q17.
Definition q19 : St -> St := D q18.
Definition q20 : St -> St := D q19.
Time CoFixpoint r : St := match false with true => q20 r | false => c r end.
