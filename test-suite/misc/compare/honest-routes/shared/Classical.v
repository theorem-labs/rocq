(* A library of the image's own, which challenge and answer both load from
   one file and the config does not pre-check: a stand-in for the standard
   library's Classical_Prop. *)

Axiom classic : forall P : Prop, P \/ ~ P.
