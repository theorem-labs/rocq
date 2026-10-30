(* Constants and an inductive of a required library. The edited tree changes
   one property of each: the type of t1, the body of t2, the universe
   constraint of t3, the typing flags of t4, the constructors of i5. t0 does
   not change. *)
Definition t0 := 0.
Definition t1 : (fun T => T) nat := 0.
Definition t2 := 1.
Polymorphic Definition t3@{u v | u < v} (A : Type@{u}) : Type@{v} := A.
#[bypass_check(guard)] Definition t4 := 0.
Inductive i5 := C5 | D5.
