- **Changed:**
  :cmd:`Print Assumptions` and the ``Print … Dependencies`` commands reuse
  the traversal of an object across queries made in the same global
  environment, so a file that runs many queries walks each object once;
  the output is unchanged, and the ``assumptions-memo`` debug flag reports
  each reuse
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
