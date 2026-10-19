- **Added:**
  ``rocqchk -j n`` checks opaque proofs in parallel, in worker processes
  created with ``fork``: up to *n*-1 while the main process checks the
  rest, then up to *n* while it waits for them.
  A worker stops after ``-worker-budget s`` seconds (default 20) and its
  unchecked proofs are given to another process, which bounds the memory
  that workers copy from the main process
  (see :ref:`rocqchk`)
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Jason Gross, building on the deferred checking of opaque proofs of
  `#22520 <https://github.com/rocq-prover/rocq/pull/22520>`_ by Gaëtan Gilbert).
