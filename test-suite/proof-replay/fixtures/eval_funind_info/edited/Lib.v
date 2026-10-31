(* The name h_rec is taken before Function h runs, so Function declares h,
   R_h, h_rect and h_ind as in the original tree, cannot declare h_rec, and
   never gives h an entry in the funind table. g and its entry do not
   change. *)
Declare ML Module "rocq-runtime.plugins.funind".

Function g (n : nat) : nat := match n with 0 => 0 | S m => g m end.

Definition h_rec := 0.

Function h (n : nat) : nat := match n with 0 => 0 | S m => h m end.
