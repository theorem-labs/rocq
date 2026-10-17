#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 23. ACCEPTED OVER-REFUSAL (asserted
# reused through round 22). Same reason as cx1_export_disjoint_overrefused:
# a disjoint new export grows A's loaded-library list, and round 23 refuses
# any change to that list (a hidden global instance or hint would change a
# fresh dependent); this library carries none, so a fresh B compiles.
. ../round16-lib.sh
uc_round16 overrefused
