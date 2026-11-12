(* One copy of colour, with a function on it. *)
Inductive colour := Red | Blue.

Definition flip (c : colour) : colour :=
  match c with Red => Blue | Blue => Red end.
