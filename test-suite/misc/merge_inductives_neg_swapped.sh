#!/usr/bin/env bash

# Same constructors, other order: the agent's [color] is [Green | Red] where
# the spec's is [Red | Green]. The names match as a set and nothing else about
# the two blocks differs, so this is the case a merge that compared names
# without their positions would get wrong. It must not merge.
#
# There is no False to be had here, and the test does not pretend otherwise:
# swapping two constructors of the same type is an automorphism of it, so
# everything the agent proves stays true of the spec's type under the swap
# (read [Agent.Red] as [Spec.Green] throughout and the agent's library is a
# model of itself). Checker.v is instead a detector: the agent's
# [Green <> Red] becomes the spec's [Red <> Green] exactly when the merge is
# granted, so the test fails loudly the moment the comparison stops looking at
# constructor positions.
set -eu

. misc/merge_inductives_common.bash

mi_negative misc/merge_inductives_neg_swapped
