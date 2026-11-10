#!/usr/bin/env bash

# Block size: the spec declares [even] and [odd] in one mutual block, the
# agent declares the same two types, word for word, in two blocks of one.
# A merge is of whole blocks, so the agent's [even] must not take the spec's
# name.
#
# The brief for this case had the agent declare [even] alone. That cannot be
# written while the spec's two types refer to each other -- [odd] would be
# undefined -- so the two types here are independent, which isolates the one
# difference the case is about: how they are grouped.
#
# No False witness: the test pins that Checker.v is refused.
set -eu

. misc/merge_inductives_common.bash

mi_negative misc/merge_inductives_neg_mutual
