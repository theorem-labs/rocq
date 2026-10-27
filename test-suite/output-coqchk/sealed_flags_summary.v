(* The other unsafe flags behind an opaque seal: type-in-type on a constant
   and an assumed positivity on an inductive. *)
Module Type T. Parameter t : Type. End T.
Module Seal : T.
  #[bypass_check(positivity)] Inductive bad := C : (bad -> False) -> bad.
  #[bypass_check(universes)] Definition t : Type := Type.
End Seal.
