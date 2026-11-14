(* The honest library that misc/rocqchk_functor_loop_summary.sh compiles,
   and that forge.ml then makes a functor whose body applies that functor
   again, which coqc refuses to write:
     Module Grow := F Loc.
   R applies F, so the -o summary reads F's body as R's. There F's own path
   names R, so the walk reads Grow as F A applied to R.Loc: two arguments
   for F's one parameter. The walk is refused there. *)
Inductive unit : Set := tt.

Module Type S. End S.
Module A. End A.
Module G (X : S). End G.

Module F (X : S).
  Axiom ax : unit.
  Module Loc. End Loc.
  Module Grow := G Loc.
End F.

Module R := F A.
