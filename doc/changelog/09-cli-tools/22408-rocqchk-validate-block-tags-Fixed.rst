- **Fixed:**
  ``rocqchk``'s value validator now admits only the tags of non-constant
  constructors where a record, tuple or array is expected; it also admitted
  ``Obj.no_scan_tag`` and the GC-special tags
  (`#22408 <https://github.com/rocq-prover/rocq/pull/22408>`_,
  fixes `#22407 <https://github.com/rocq-prover/rocq/issues/22407>`_,
  by Pierre-Marie Pédrot).
