- **Changed:**
  :tacn:`lia` and :tacn:`nia` search faster, with the same certificates and failures: a problem
  that the search already solved in the same process gets the earlier result (also with the
  cache files off), and the elimination of linear equalities before the search no longer
  pivots or simplifies again a constraint that the substituted variable does not occur in
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
