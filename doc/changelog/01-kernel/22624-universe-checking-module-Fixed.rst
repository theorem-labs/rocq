- **Fixed:**
  After a module that locally unset universe checking is closed, the universe
  graph again checks universe constraints; its own copy of the flag could stay
  out of step with the environment's typing flags
  (`#22624 <https://github.com/rocq-prover/rocq/pull/22624>`_,
  fixes `#22287 <https://github.com/rocq-prover/rocq/issues/22287>`_,
  by Gaëtan Gilbert).
