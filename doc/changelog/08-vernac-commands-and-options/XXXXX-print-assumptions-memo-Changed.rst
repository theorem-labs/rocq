- **Changed:**
  :cmd:`Print Assumptions`, :cmd:`Print Opaque Dependencies`,
  :cmd:`Print Transparent Dependencies` and :cmd:`Print All Dependencies`
  reuse the traversal of an object across consecutive queries with no
  declaration between them, so such queries need not walk again the objects
  they share. The output is byte-identical wherever the traversal without
  reuse finishes normally. When a query starts, what the reuse keeps weighs
  at most four times the traversal data of the largest earlier query in the
  environment, and it is cleared when it would weigh more; so peak memory
  exceeds that of the traversal without reuse by at most about five times
  the largest query's traversal data. Recording a walk for reuse costs time
  on the query that first makes it, up to about three times the walk on
  inductive blocks with hundreds of thousands of constructors, so a query
  under a tight ``Timeout`` can run out of time where the traversal without
  reuse would not; on the shapes the test suite checks, a file with queries
  compiles in at most three times the CPU time of the same file without
  them, plus one second. Setting the environment variable
  ``ROCQ_DEBUG_ASSUMPTIONS_MEMO=1`` reports each reuse on standard error
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_).
