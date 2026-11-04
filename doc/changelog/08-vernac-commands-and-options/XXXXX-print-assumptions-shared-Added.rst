- **Added:**
  the environment variable ``ROCQ_ASSUMPTIONS_SHARED_DIR``. When it names a
  directory, :cmd:`Print Assumptions`, :cmd:`Print Opaque Dependencies`,
  :cmd:`Print Transparent Dependencies` and :cmd:`Print All Dependencies`
  share the traversal of an object with every other process that names the
  same directory, so a set of processes that query the same libraries walk
  each of their objects once between them. Each process keeps what it reads
  and writes only while it keeps the traversals it reuses, so the memory
  above holds. The output is the output without sharing: a traversal is
  shared only between processes that load, for the libraries of the object's
  two names and for every library those depend on, the same declarations and
  the same opaque proofs, as the digests the files record tell. A directory
  must hold only what the processes of one build over one set of library
  files wrote: a process reads an entry with ``Marshal`` after checking a
  digest, which catches a damaged file but not one written to deceive it.
  Sharing costs a file created and written per object, so it pays where
  objects are few and expensive, and loses where they are many and cheap.
  Two differences from a query without sharing remain, both in the
  direction of answering more often: a query collects the traversals one
  object at a time and then replays them, where a query without sharing
  holds one stack frame per object, so a query over a chain of tens of
  thousands of objects can answer where one without sharing runs out of
  stack; and the collecting itself takes time that a ``Timeout`` around the
  query counts.
  Setting ``ROCQ_DEBUG_ASSUMPTIONS_SHARED=1`` reports, per query, how many
  objects were walked, read from the directory, already held, waited for and
  taken over from a process that ended, on standard error
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_).
