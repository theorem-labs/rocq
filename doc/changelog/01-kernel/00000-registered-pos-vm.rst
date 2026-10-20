- **Added:**
  Kernel registrations for the Corelib ``positive`` operations
  ``Pos.compare_cont``, ``Pos.eqb``, ``Pos.add``, ``Pos.succ``, and
  ``Pos.mul``. The bytecode VM recognizes a validated registration and uses
  native evaluation for fully evaluated positive arguments.
