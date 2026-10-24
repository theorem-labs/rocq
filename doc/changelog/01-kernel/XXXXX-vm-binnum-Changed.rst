- **Changed:**
  The bytecode VM runs the functions on binary and unary numbers of Corelib
  as C routines: ``Pos.compare_cont``, ``eqb``, ``succ``, ``add``,
  ``add_carry``, ``pred_double``, ``mul``, ``div2``, ``of_succ_nat``;
  ``Z.double``, ``succ_double``, ``pred_double``, ``pos_sub``, ``add``,
  ``mul``, ``compare``, ``leb``, ``ltb``, ``eqb``, ``div2``, ``of_nat``,
  ``pos_div_eucl``, ``pow``; ``Nat.eqb`` and ``leb``; and ``to_Z_rec`` and
  ``of_pos_rec`` of ``Uint63Axioms``, between primitive integers and binary
  numbers.
  When the bytecode compiler finds a constant whose body is equal to one of
  these functions (also over other inductive types of the same shapes, and
  with callees whose bodies are in turn equal to the expected functions), it
  puts a new instruction, ``BINNUM``, at the start of the code of the
  function, and a second one, ``BINNUMCALL``, at each call of the constant
  with all its arguments. The instructions compute the result when every
  node of the arguments that the function reads is a constructor, and the
  bytecode of the body or of the call computes it otherwise. The other
  opcodes keep their numbers, so this build loads the code of ``.vo`` files
  written by earlier builds; a ``.vo`` file written by this build can hold
  ``BINNUM`` and ``BINNUMCALL``, which earlier builds cannot load.
  On 64-bit builds with OCaml before 5.0, the VM also holds a number of 2
  to 62 bits, which a routine computes or which a term writes out, as one
  block: the routines read it as a number, and the rest of the VM as the
  chain of its constructors
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
