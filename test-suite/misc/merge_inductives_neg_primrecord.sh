#!/usr/bin/env bash

# The same record, primitive on one side and regular on the other. Nothing in
# the declaration's text differs; what differs is the record-ness the kernel
# records for the block, and with it whether the projections are primitive and
# whether the type has definitional eta.
#
# No False witness: what a wrongly granted merge would break here is the
# representation of projections, not consistency, so the test pins that
# Checker.v is refused.
set -eu

. misc/merge_inductives_common.bash

mi_negative misc/merge_inductives_neg_primrecord
