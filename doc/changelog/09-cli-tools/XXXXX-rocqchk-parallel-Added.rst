- **Added:**
  ``rocqchk -j n`` checks opaque proofs in parallel, in up to *n*-1 worker
  processes created with ``fork``, while the main process checks the rest
  (see :ref:`rocqchk`)
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Jason Gross, building on the deferred checking of opaque proofs of
  `#22520 <https://github.com/rocq-prover/rocq/pull/22520>`_ by Gaëtan Gilbert).
