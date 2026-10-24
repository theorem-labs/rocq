- **Added:**
  ``rocqchk -statement-report file`` prints, for each request in *file*,
  whether a constant has the type of another constant and the axioms and
  unsafe flags that its closure uses, after checking. The closure goes
  through the bodies that module signatures hide, as
  :cmd:`Print Assumptions` does
  (see :ref:`rocqchk`)
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
