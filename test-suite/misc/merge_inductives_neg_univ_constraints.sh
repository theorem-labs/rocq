#!/usr/bin/env bash

# Two copies whose universe constraints differ: both blocks are polymorphic in
# [u] and [v], and the agent's carries [u <= v] where the spec's carries
# nothing. Everything else -- names, parameters, the constructor's type -- is
# the same, and both statements are written at the same instance, [Set Set],
# which satisfies the agent's constraint, so the constraint is the only thing
# left to compare.
#
# No False witness: the test pins that Checker.v is refused.
#
# merge_inductives_shared_level_constraint.sh is the other half of this: there
# the blocks are monomorphic and the constraint that differs is against a
# level both libraries share.
set -eu

. misc/merge_inductives_common.bash

mi_negative misc/merge_inductives_neg_univ_constraints
