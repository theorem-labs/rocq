Require Import Ltac2.Ltac2.

(** Backtrace frames of Ltac2 functions whose bodies run as direct code while backtraces are off:
    once [Set Ltac2 Backtrace] is on, the frames of calls nested in an argument, in a let and
    under a constructor appear, down to the call that fails. *)

Ltac2 Type exn ::= [ E ].
Ltac2 fail_at (x : int) := if Int.equal x 0 then Control.throw E else x.
Ltac2 in_arg (x : int) := Int.add 1 (Int.mul 2 (fail_at x)).
Ltac2 in_let (x : int) := let y := in_arg x in Int.add y 1.
Ltac2 in_ctor (x : int) := [in_let 1; in_let x].

(** With backtraces off, the same calls run. *)
Ltac2 Eval in_ctor 1.
Fail Ltac2 Eval in_ctor 0.

Set Ltac2 Backtrace.
Fail Ltac2 Eval in_ctor 0.
Unset Ltac2 Backtrace.
Fail Ltac2 Eval in_ctor 0.
