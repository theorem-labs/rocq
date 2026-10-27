(* Two cofixpoints that the guard checker must refuse. Each of them gives a
   closed proof of False that uses no axiom and no typing flag, and the kernel
   re-check (rocqchk) reports nothing, so a grader that reads axioms and unsafe
   flags sees a clean proof (binary-equivalence-taiga, dispatch://BET-214). *)

(* rocq-prover/rocq#22386: the recursion tree of the block was computed from
   the type of the first body, in the environment of the whole block, so the
   local definitions above the cofixpoint chose the tree. The tree of Stream
   was used to accept a cofixpoint that builds the inductive type Empty. *)
CoInductive Stream : Type := next : Stream -> Stream.
Inductive Empty : Type := wrap : Empty -> Empty.
Fail Definition cycle : Empty :=
  let actual := Empty in
  let decoy := Stream in
  cofix recur : actual := wrap recur.

(* rocq-prover/rocq#22389: in a nested mutual cofixpoint, a recursive call to
   the outer cofixpoint was allowed in a body other than the one the block
   selects, which is never guarded by a constructor of the outer type. *)
CoInductive D (X Y : Type) := dc : X -> Y -> D X Y.
CoInductive C (A : Type) := cc : C A -> D (C A) A -> C A.
Inductive I : Type := ic : C I -> I.
Fail CoFixpoint cycle2 : C I :=
  (cofix f : C I := cc I f g
   with g : D (C I) I := dc (C I) I cycle2 (ic cycle2)
   for f).
