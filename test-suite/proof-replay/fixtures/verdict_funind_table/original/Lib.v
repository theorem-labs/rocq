(* Function defines f, its graph R_f and the principles f_rect, f_ind and
   f_rec, and then gives f an entry in the funind table. functional
   induction (B.v) finds f_ind through that entry. *)
Declare ML Module "rocq-runtime.plugins.funind".

Function f (n : nat) : nat := match n with 0 => 0 | S m => f m end.
