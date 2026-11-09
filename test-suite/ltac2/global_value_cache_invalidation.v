(* The value of a global changes when the tables the interpreter reads change: a redefinition of a
   mutable global, the end of the scope a redefinition belongs to, a Reset, each application of a
   functor, and the state a failed command leaves behind. Each evaluation below must see the value
   of the global as the table holds it at that point.

   These are r2-b's adversarial inputs for the cache of global values (dispatch://INFRA-217), kept
   as tests. Every global they read is of a shape the interpreter may keep (a closure or an
   integer), so they fail on a cache that keeps a value across a write to the tables: without the
   test of the globals table's identity, the module, section, Reset and functor tests below all
   fail. *)

Require Import Ltac2.Ltac2.

Ltac2 assert_eq_int x y := Control.assert_true (Int.equal x y).

(* A redefinition belongs to the scope that made it. *)
Module Original.
  Ltac2 mutable x () := 0.
  Ltac2 y () := x ().
End Original.

Ltac2 Eval assert_eq_int (Original.y ()) 0.

Module Change.
  Ltac2 Set Original.x := fun () => 1.
  Ltac2 Eval assert_eq_int (Original.y ()) 1.
End Change.

Ltac2 Eval assert_eq_int (Original.y ()) 0.

Module ImportedChange.
  Import Change.
  Ltac2 Eval assert_eq_int (Original.y ()) 1.
End ImportedChange.

(* Closing a section undoes a local redefinition. *)
Ltac2 mutable sx () := 0.
Ltac2 sy () := sx ().

Ltac2 Eval assert_eq_int (sy ()) 0.

Section LocalMutation.
  #[local] Ltac2 Set sx := fun () => 1.
  Ltac2 Eval assert_eq_int (sy ()) 1.
End LocalMutation.

Ltac2 Eval assert_eq_int (sy ()) 0.

(* A failed command leaves the value as it was. *)
Fail Ltac2 Set sx := 1.

Ltac2 Eval assert_eq_int (sy ()) 0.

(* Each application of a functor has its own globals, and the redefinition inside the functor's
   body is not exported by either application. *)
Module Type ARG.
End ARG.

Module F (X : ARG).
  Ltac2 mutable fx () := 0.
  Ltac2 fy () := fx ().
  Ltac2 Eval assert_eq_int (fy ()) 0.
  Ltac2 Set fx := fun () => 1.
  Ltac2 Eval assert_eq_int (fy ()) 1.
End F.

Module A <: ARG.
End A.

Module B <: ARG.
End B.

Module FA := F A.
Module FB := F B.

Ltac2 Eval assert_eq_int (FA.fy ()) 0.
Ltac2 Eval assert_eq_int (FB.fy ()) 0.

(* Reset removes the definition, and the name is defined again. *)
Ltac2 reset_value := 0.

Ltac2 Eval assert_eq_int reset_value 0.

Reset reset_value.

Ltac2 reset_value := 1.

Ltac2 Eval assert_eq_int reset_value 1.
