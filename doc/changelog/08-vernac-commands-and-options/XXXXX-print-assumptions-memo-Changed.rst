- **Changed:**
  :cmd:`Print Assumptions`, :cmd:`Print Opaque Dependencies`,
  :cmd:`Print Transparent Dependencies` and :cmd:`Print All Dependencies`
  reuse the traversal of an object across consecutive queries with no
  declaration between them, so such queries need not walk again the objects
  they share. The output is byte-identical wherever the traversal without
  reuse finishes normally. What the reuse keeps is cleared, at the start of
  a query, when it weighs more than twice the traversal data of the largest
  earlier query in the environment. For an object it keeps about what the
  traversal keeps for it: for an axiom, a parameter or an ``Admitted`` lemma
  no reference at all (the traversal keeps none), and for an inductive
  block one more set, its references plus its members. A query that replays
  such objects collects the references of their types again and holds each
  once, so peak memory exceeds that of the traversal without reuse by at
  most about three times the largest query's traversal data, within a query
  as well as between queries. Recording a walk for reuse costs time on the
  query that first makes it, up to about three times the walk on inductive
  blocks with hundreds of thousands of constructors, so a query under a
  tight ``Timeout`` can run out of time where the traversal without reuse
  would not, and replaying a very wide inductive block, or the type of an
  axiom that names very many objects, can cost more than walking it. On the
  shapes the test suite checks, a file with queries compiles in at most three
  times the CPU time of the same file without them, plus one second, and a
  query that replays thousands of axioms with wide types takes at most three
  times as long as the query that recorded them, plus one second. Setting the
  environment variable ``ROCQ_DEBUG_ASSUMPTIONS_MEMO=1`` reports each reuse,
  and each clearing of what the reuse keeps, on standard error
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_).
