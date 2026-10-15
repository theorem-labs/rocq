# g1_admitted_to_qed_reused (binary-equivalence-taiga#841 G1)

Scenario: A.v has `Lemma p : t. Admitted.` plus `Definition g := I1.`; B.v requires A
and uses only `g` (`Definition b := g.`), never `p`. A is edited so `p` goes
`Admitted -> Qed` (any valid proof). Expected: B.vo is REUSED (the G1 fix
excludes the CONSTANT libobject's `cst_kind` field from the exact-equality
objects digest, since it's presentational/live-queried, not load-bearing for an
already-elaborated dependent -- see declaremods.ml's `G1Partition` module doc
comment). Before this fix, this scenario was REFUSED, defeating the lever's
whole purpose.
