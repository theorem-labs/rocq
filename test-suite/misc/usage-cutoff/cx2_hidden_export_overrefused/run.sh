#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 23. ACCEPTED OVER-REFUSAL (asserted
# reused through round 22). Same reason as cx1_export_disjoint_overrefused:
# A's loaded-library list changes, which round 23 refuses because a hidden
# library carrying a #[global] instance or hint would change a fresh
# dependent's resolution; this one carries none, so a fresh B compiles.
. ../round16-lib.sh
uc_round16 overrefused
