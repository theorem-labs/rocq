(* The name f_rec is taken before Function runs. Function declares f, R_f,
   f_rect and f_ind as in the original tree, then cannot declare f_rec: it
   gives a warning, stops, and never gives f an entry in the funind table.
   So every constant the proof in B.v reads is the same as at registration,
   and only the table entry is gone (gate review of 079bc4cb71, breadth
   audit). *)
Declare ML Module "rocq-runtime.plugins.funind".

Definition f_rec := 0.

Function f (n : nat) : nat := match n with 0 => 0 | S m => f m end.
