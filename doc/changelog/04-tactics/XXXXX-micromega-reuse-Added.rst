- **Added:**
  flag :flag:`Micromega Reuse` (set by default). With it, :tacn:`lia`, :tacn:`nia`, :tacn:`wlia`
  and :tacn:`wnia`
  try the certificates they found for the earlier cases of a goal, such as the two sides of
  a disjunction, before they search for a certificate of the next case, so they fail sooner on
  a goal that they cannot prove. When the tactic succeeds, it searches the cases that a reused
  certificate proved, so its proof is the proof without the flag. The tries take at most about
  6% of the time of the searches of a goal, so a goal that succeeds is at most that much slower
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
