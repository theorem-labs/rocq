- **Fixed:**
  The guard checker accepted some nested fixpoints whose inner arguments are
  not uniform, which gave a closed proof of :g:`False`: the arguments of a
  recursive call were not analysed, and a local definition in the prefix of an
  inner fixpoint was counted as a formal argument. Backport of
  (`#21798 <https://github.com/rocq-prover/rocq/pull/21798>`_,
  fixes `#21797 <https://github.com/rocq-prover/rocq/issues/21797>`_,
  by Pierre-Marie Pédrot),
  (`#22384 <https://github.com/rocq-prover/rocq/pull/22384>`_,
  fixes `#22382 <https://github.com/rocq-prover/rocq/issues/22382>`_,
  by Yann Leray)
  and (`#22022 <https://github.com/rocq-prover/rocq/pull/22022>`_,
  fixes `#22021 <https://github.com/rocq-prover/rocq/issues/22021>`_,
  by Yann Leray), which also checks the domain of a lambda in a nested
  fixpoint body when the stack is empty.
