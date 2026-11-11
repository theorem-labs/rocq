#!/usr/bin/env bash

# The shape the grader actually runs rocqchk in: it names only the agent's
# libraries and the checker files with -norec, so OUR statement library is
# not listed and is loaded unchecked, as a dependency. A library loaded that
# way must still take part in merges -- it is already trusted whole, so
# merging against it adds no trust, and refusing would refuse the use case.
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_grader_shape

mi_coqc Spec -merge-inductives
mi_coqc Agent -merge-inductives
mi_coqc Checker -merge-inductives

# Spec is not listed: it arrives unchecked.
mi_rocqchk -merge-inductives -o -norec "$mi_root.Agent" -norec "$mi_root.Checker"

# Agent unchecked too: only the checker file is checked.
mi_rocqchk -merge-inductives -o -norec "$mi_root.Checker"

# Without the option the same run must be refused.
mi_rocqchk_fails -o -norec "$mi_root.Agent" -norec "$mi_root.Checker"
