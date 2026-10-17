#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 23 adversarial review (load-order-continuation.md,
# case `order-hidden-instance-interface`), sources verbatim. A inserts or reorders a plain, non-exported Require of a library carrying a #[global] instance or hint. B's fresh resolution changes; the subsequence load-order rule accepted the stale B.
. ../adv-lib.sh
uc_adv_refused X.v I0.v I1.v
