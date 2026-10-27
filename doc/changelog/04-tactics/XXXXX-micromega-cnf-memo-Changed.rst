- **Changed:**
  :tacn:`lia`, :tacn:`nia`, :tacn:`lra`, :tacn:`nra` and :tacn:`psatz` convert their goal to
  conjunctive normal form faster, with the same result: the check of whether two constraints of
  a clause contradict each other is computed once per pair of constraints, where the conversion
  met the same pair in many clauses
  (`#XXXXX <https://github.com/rocq-prover/rocq/pull/XXXXX>`_,
  by Sami Jawhar).
