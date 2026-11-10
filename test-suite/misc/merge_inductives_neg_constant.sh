#!/usr/bin/env bash

# A constructor type mentioning a constant that has the same short name in
# each file but a different definition: Spec.f is nat, Agent.f is bool. The
# two blocks must not be merged.
#
# No False witness: the test pins that Checker.v is refused.
set -eu

. misc/merge_inductives_common.bash

mi_negative misc/merge_inductives_neg_constant
