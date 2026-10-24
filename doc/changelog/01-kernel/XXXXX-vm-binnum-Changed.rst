- **Changed:**
  The bytecode VM runs ``Pos.compare_cont`` and ``Pos.eqb`` as C routines.
  When the bytecode compiler finds a constant whose body is equal to one of
  these functions (also over another inductive type of the same shape as
  ``positive``), it puts a new instruction, ``BINNUM``, at the start of the
  code of the function. The instruction computes the result when every
  argument is a closed number, and the bytecode of the body computes it
  otherwise. The other opcodes keep their numbers, so this build loads the
  code of ``.vo`` files written by earlier builds; a ``.vo`` file written by
  this build can hold ``BINNUM``, which earlier builds cannot load
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
