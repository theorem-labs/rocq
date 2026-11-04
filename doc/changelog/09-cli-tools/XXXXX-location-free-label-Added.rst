- **Added:**
  ``rocq compile -location-free-label`` stores, as the digest of a
  library's ``library`` segment, the first 16 bytes of a location-free
  label: the SHA-256 of the library's compiled form, its object segments
  with their source locations removed, its attempted resolutions that
  nothing else records, and its summary (its name, its direct
  dependencies with their digests, which of them it only safe-required
  with ``Require (safe)``, and its attributes). A rebuild that only moves
  text, or only changes an opaque proof without creating a universe, keeps
  the label, so ``rocq compile`` and ``rocqchk`` accept the dependents
  compiled against the previous build. Without the option the file is
  unchanged. The new executable ``rocq-library-label`` recomputes the
  label from a ``.vo`` file's content (``--check`` prints ``label2``, then
  the 32-byte label; ``md5`` for a file with stock's digest; ``other``
  otherwise) and prints its attempted-resolution records, as text
  (``--attempts``) or as JSON (``--attempts-json``)
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
