#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 23. The copied library is NOT a direct
# requirement of B: B requires R, R re-exports A, and B Includes A. A's
# entry is absent from B's own root dependency array, so the per-dependency
# check never visits it, and R itself is reused (A only gained a Module
# Type). The structural record is keyed by the copied library, not by the
# root list, which is what makes this case reachable at all.
. ../structural-copy-lib.sh
uc_structural_copy_refused P.v ok
