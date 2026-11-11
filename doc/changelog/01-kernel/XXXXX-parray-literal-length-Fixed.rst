- **Fixed:**
  The kernel now refuses a primitive array literal longer than
  `PrimArray.max_length`. Lazy reduction truncated such a literal to
  `max_length` while the virtual machine and native compilation kept it
  whole, so its length could be proved to have two different values
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
