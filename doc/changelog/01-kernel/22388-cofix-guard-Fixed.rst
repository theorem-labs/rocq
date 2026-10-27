- **Fixed:**
  The guard checker accepted two families of cofixpoints that give a closed
  proof of :g:`False`: the recursion tree of a cofixpoint block was computed
  from the first body's type and in the wrong environment, and a recursive
  call was allowed in a body other than the main one of a nested mutual
  cofixpoint. Backport of
  (`#22388 <https://github.com/rocq-prover/rocq/pull/22388>`_,
  fixes `#22386 <https://github.com/rocq-prover/rocq/issues/22386>`_)
  and (`#22392 <https://github.com/rocq-prover/rocq/pull/22392>`_,
  fixes `#22389 <https://github.com/rocq-prover/rocq/issues/22389>`_,
  by Pierre-Marie Pédrot).
