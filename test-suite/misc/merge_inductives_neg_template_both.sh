#!/usr/bin/env bash

# Two template-polymorphic blocks that are identical word for word. v1
# never merges a template-polymorphic block, whatever the comparison says
# about it, so the two copies stay two types and Checker.v is refused.
#
# No False witness: the test pins that Checker.v is refused.
set -eu

. misc/merge_inductives_common.bash

mi_negative misc/merge_inductives_neg_template_both
