Require Import Ltac2.Ltac2.

(** Backtrace frames around pure primitives: an exception raised in an argument of a pure primitive
    carries the frames of every Ltac2 function it went through, and the backtrace printed inside an
    argument is the one of the calls around it. *)

Set Ltac2 Backtrace.

Ltac2 fail_in (x : int) : int := let _ := x in Control.throw (Invalid_argument None).
Ltac2 g (x : int) := Int.add (Int.mul x 2) (fail_in (Int.sub x 1)).
Ltac2 h () := match Int.equal (g 3) 0 with true => 1 | false => 2 end.
Fail Ltac2 Eval h ().

Ltac2 l () := let y := Int.sub (g 1) 1 in Int.add y 1.
Fail Ltac2 Eval l ().

Ltac2 print_stack () := Message.print (Message.of_exninfo (Control.current_exninfo ())).
Ltac2 k (x : int) := Int.add x (print_stack (); 1).
Ltac2 m () := let y := k (Int.sub 5 2) in Int.add y 1.
Ltac2 Eval m ().
