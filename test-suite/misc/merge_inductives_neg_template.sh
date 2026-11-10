#!/usr/bin/env bash

# The same block, template polymorphic on one side and not on the other. The
# two declarations read the same; what differs is the universe machinery the
# kernel keeps for the block, which decides at which universes the type may be
# instantiated.
#
# No False witness: the test pins that Checker.v is refused.
set -eu

. misc/merge_inductives_common.bash

mi_negative misc/merge_inductives_neg_template
