(* A library both sides share, declared pre-checked in the config. It
   stands for the standard library: its universe levels are the same object
   on the two sides, so the level map holds the identity on them, and a
   constraint an answer adds between a level of its own and one of these is
   a constraint between two mapped levels. *)

Definition Shared : Type := Type.
