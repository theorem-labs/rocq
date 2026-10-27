- **Changed:**
  the Ltac2 interpreter is faster, with the same results: it caches the values of global
  Ltac2 definitions, finds ML primitives and local variables faster, and evaluates the
  arguments of an application in one step, instead of through the proof monad, when they are
  all literals, variables, functions, primitives, or small constructors and projections of such;
  once a tactic runs, it also computes calls to pure primitives (such as ``Int.equal`` or
  ``Constr.Unsafe.kind``), and the lets, matches and arguments around them, without the proof
  monad's binds, and runs the body of an Ltac2 function applied to all its arguments at once,
  with the code after the call; the bodies of global Ltac2 functions, and of the functions
  written inside them, are turned once into OCaml closures that run them, with each local
  variable read at its known position, and a partial application keeps that fast path
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
