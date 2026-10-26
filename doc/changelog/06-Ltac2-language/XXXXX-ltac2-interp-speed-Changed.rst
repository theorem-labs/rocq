- **Changed:**
  the Ltac2 interpreter is faster, with the same results: it caches the values of global
  Ltac2 definitions, finds ML primitives and local variables faster, and evaluates the
  arguments of an application in one step, instead of through the proof monad, when they are
  all literals, variables, functions, primitives, or small constructors and projections of such
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
