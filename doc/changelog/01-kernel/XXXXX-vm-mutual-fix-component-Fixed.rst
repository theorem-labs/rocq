- **Fixed:**
  VM conversion no longer loses the component index of a mutual fixpoint when
  it expands a stuck value on the fly: it enters the fixpoint's bytecode with
  that component's own closure instead of the block's last component, which the
  ``GRABREC`` instruction would otherwise record in the accumulator it builds.
  A component of a mutual block was not convertible with its own
  eta-expansion, and the last component of a block was convertible with any
  other component of the same block, so a ``vm_compute`` or ``native_compute``
  cast could prove a false equation between two different functions and hence
  ``False``; a single-component fixpoint was unaffected
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
