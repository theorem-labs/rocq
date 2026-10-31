(* Two functions, each with its entry in the funind table. *)
Declare ML Module "rocq-runtime.plugins.funind".

Function g (n : nat) : nat := match n with 0 => 0 | S m => g m end.

Function h (n : nat) : nat := match n with 0 => 0 | S m => h m end.
