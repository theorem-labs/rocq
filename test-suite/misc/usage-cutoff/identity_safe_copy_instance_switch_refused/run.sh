#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 23 adversarial review (structural-continuation.md,
# case `identity-safe-copy-instance-switch`), sources verbatim. A switches a requirement between Require and Require (safe), which decides whether its global instances and hints load. B Includes A. md_safe_deps was in no compared digest, so the stale B was accepted.
. ../adv-lib.sh
uc_adv_refused X.v I0.v I1.v
