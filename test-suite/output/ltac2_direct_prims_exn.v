Require Import Ltac2.Ltac2.

(** Fatal exceptions ([Control.throw], and those of primitives such as [Array.get] and [Int.div])
    raised in an argument of a pure primitive: the arguments before it run (they print), the
    arguments after it and the primitive do not ("never" is not printed), and the error is the
    exception raised. *)

Ltac2 say (s : string) := Message.print (Message.of_string s).

Fail Ltac2 Eval Int.add (say "first"; 0) (Int.add (Array.get (Array.make 2 0) 5) (say "never"; 1)).
Fail Ltac2 Eval let x := Int.sub (say "first"; 1) (Int.div 1 0) in say "never"; x.
Fail Ltac2 Eval
  match Int.equal (say "first"; 0) (Control.throw (Invalid_argument (Some (Message.of_string "arg")))) with
  | true => say "never"
  | false => say "never"
  end.
Fail Ltac2 Eval Int.add (Control.throw Not_found) (say "never"; 1).
