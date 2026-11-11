#!/usr/bin/env bash

# A block with one constructor more does not match: the agent's [color] has
# Red, Green and Blue where the spec's has Red and Green.
#
# Bad.v is the witness of what the refusal buys. Spec proves that its colour
# is Red or Green; the agent's Blue is neither. Were the two blocks merged,
# Bad.v would prove False, so it must be refused too.
set -eu

. misc/merge_inductives_common.bash

mi_negative misc/merge_inductives_neg_extra_ctor

mi_coqc_fails Bad -merge-inductives
