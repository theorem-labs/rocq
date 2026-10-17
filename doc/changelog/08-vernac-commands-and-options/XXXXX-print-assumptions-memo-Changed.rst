- **Changed:**
  :cmd:`Print Assumptions`, :cmd:`Print Opaque Dependencies`,
  :cmd:`Print Transparent Dependencies` and :cmd:`Print All Dependencies`
  reuse the traversal of an object across consecutive queries with no
  declaration between them, so such queries walk the objects they share
  once. The output is byte-identical wherever the traversal without reuse
  finishes normally, and the reuse never makes a query fail that it answers;
  setting the environment variable ``ROCQ_DEBUG_ASSUMPTIONS_MEMO=1`` reports
  each reuse on standard error
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
