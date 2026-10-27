- **Changed:**
  :tacn:`lia` and :tacn:`nia` prepare consecutive problems that share most of their constraints
  faster, with the same certificates and failures: a developed constraint is kept in a memo,
  the elimination of linear equalities reuses the rounds of the previous problem when only one
  inequality changed, the bounds on monomials are not looked for in linear problems, and Fourier's
  elimination builds a proof only for the constraints it keeps
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
