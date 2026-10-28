(* The checked statement library. It does NOT Require StmtAdmit.Model, so when
   Model is admitted it is a dependency of no checked library -- the shape that
   triggered the anomaly. Built with -noinit so it depends on nothing. *)

Inductive snat : Set := sO : snat | sS : forall _ : snat, snat.
Definition t : snat := sO.
