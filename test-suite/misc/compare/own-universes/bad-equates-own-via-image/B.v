(* bad-equates-own routed through one of the image's levels. No constraint
   here relates two of the challenge's universes directly -- each one
   touches Img.W.w -- and together they make the challenge's p and q one
   universe, which is what its statement over Type@{p} -> Type@{q} stands
   on.

   A rule that looked at the edges the answer adds, one at a time, would
   compare none of these. The rule is entailment: the answer's graph is
   projected onto the challenge's own levels, paths through the image's
   levels included, and the projection must hold in the challenge's graph.

   An agent needs no Constraint command to do this: a monomorphic type of
   the image used where Type@{p} is expected gives one of these edges, and
   one used the other way round gives the other. *)

Require Top.A.
Require Img.W.

Monomorphic Constraint Top.A.p <= Img.W.w.
Monomorphic Constraint Img.W.w <= Top.A.q.
Monomorphic Constraint Top.A.q <= Img.W.w.
Monomorphic Constraint Img.W.w <= Top.A.p.
