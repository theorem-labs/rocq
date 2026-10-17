#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 23. ACCEPTED OVER-REFUSAL (asserted
# reused through round 22). W gains a disjoint `Require Export`, so A's
# loaded-library list grows. Round 23 requires a dependency's list to be
# unchanged, because an inserted plain Require of a library carrying a
# #[global] instance or hint changes a fresh dependent's resolution with no
# export visibility at all (order_hidden_global_instance_refused and its
# siblings). The added library here carries none, so a fresh B compiles
# identically; telling the two apart would need a per-library analysis of
# global instances and hints, which the check does not attempt.
. ../round16-lib.sh
uc_round16 overrefused
