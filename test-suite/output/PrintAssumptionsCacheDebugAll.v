(* Print Assumptions reuses traversals across queries in one environment.
   Set Debug "all" turns on every debug flag; the reuse adds nothing to the
   output under it. *)

Axiom ax : Prop.
Definition f := ax.
Print Assumptions f.
Set Debug "all,-vernacinterp,-misc".
Print Assumptions f.
