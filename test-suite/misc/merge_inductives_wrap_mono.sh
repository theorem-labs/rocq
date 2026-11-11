#!/usr/bin/env bash

# merge_inductives_wrap's block, declared monomorphic: the case where each file
# owns a global universe level for its copy, so the two match only once the
# level bijection is built and the two levels are equated.
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_wrap_mono

mi_coqc Spec -merge-inductives
mi_coqc Agent -merge-inductives
mi_coqc Checker -merge-inductives

mi_rocqchk -merge-inductives MergeTest.Checker
