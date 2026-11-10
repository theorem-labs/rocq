#!/usr/bin/env bash

# A merge may equate a level each side's own library declared, and nothing
# else. Here the spec's block is written over a level a THIRD library owns
# (Shared.w) while the agent's is over its own, so the bijection would pair
# Agent.u with Shared.w -- moving a level a third party can name, and one
# the spec never promised anything about. The two blocks must not merge.
#
# Checking only that the left level belongs to the library being loaded let
# this through; both sides are checked now.
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_neg_foreign_level

mi_coqc Shared -merge-inductives
mi_coqc Spec -merge-inductives
mi_coqc Agent -merge-inductives

mi_coqc_fails Checker -merge-inductives
mi_says b "b"

mi_rocqchk -merge-inductives "$mi_root.Spec" "$mi_root.Agent"
