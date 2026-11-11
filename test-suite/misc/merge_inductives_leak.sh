#!/usr/bin/env bash

# A merge does not leak out of the run that granted it. Mid.v is compiled with
# -merge-inductives and keeps the agent's theorem under no ascription, so if
# the merged name were written into the .vo, it would be written here.
#
# It is not: a rocqchk without the option accepts Mid, and a coqc without the
# option still refuses Evil.v, which asks for Mid.d under the spec's
# statement. The refusal is about the two copies of [tree]; the two [size]
# functions are ordinary constants and were never candidates for merging.
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_leak

mi_coqc Spec -merge-inductives
mi_coqc Agent -merge-inductives
mi_coqc Mid -merge-inductives

# The .vo carries no merged name, so a checker that never heard of the option
# reads it happily.
mi_rocqchk MergeTest.Mid

mi_coqc_fails Evil
mi_says 'tree' 'the two copies of the inductive'
