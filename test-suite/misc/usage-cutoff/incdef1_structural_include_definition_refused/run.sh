#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 23. The round-22 shape with a plain
# Definition instead of a Module Type: the hole predates the empty-wrapper
# drop (4be0c270eb) and is present at fd1fa9c65b and v1 3cdc0355e0 too.
# B Includes A, A gains `z`, and a client of the copied `B.z` gets an
# anomaly against the stale B and compiles against a fresh one.
. ../structural-copy-lib.sh
uc_structural_copy_refused P.v ok
