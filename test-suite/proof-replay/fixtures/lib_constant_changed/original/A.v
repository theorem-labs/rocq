(* Constants and an inductive of a required library. The edited tree changes
   one property of each: the type of t1, the body of t2, the universe
   constraint of t3, the typing flags of t4, the constructors of i5. t0 does
   not change. *)
Definition t0 := 0.
Definition t1 : nat := 0.
Definition t2 := 0.
Polymorphic Definition t3@{u v | u <= v} (A : Type@{u}) : Type@{v} := A.
Definition t4 := 0.
Inductive i5 := C5.
