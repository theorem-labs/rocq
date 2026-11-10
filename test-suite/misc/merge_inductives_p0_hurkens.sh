#!/usr/bin/env bash

# A merge's universe equalities must reach the .vo of the library whose
# typing used them.
#
# Mid is compiled WITH the option and defines a term that type-checks only
# because Agent.box and Spec.box were merged, which also identifies the two
# libraries' universe levels. Undoing the NAMES on export is not enough: a
# reader without the option still gets the term, and if it may then assert
# Spec.u < Agent.u it has a retraction of a type into itself, from which
# Hurkens' paradox derives False (the review of 657c3716, P0; Hurkens.v here
# is that reviewer's file, kept as the control that the paradox is real).
#
# So Mid.vo records the equality, and both the short probe and the full
# paradox are refused at the Constraint line, with the option and without.
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_p0_hurkens

mi_coqc Spec -merge-inductives
mi_coqc Agent -merge-inductives
mi_coqc Mid -merge-inductives

mi_coqc_fails Evil
mi_says "Universe inconsistency" "a universe inconsistency"

mi_coqc_fails Hurkens
mi_says "Universe inconsistency" "a universe inconsistency"

# And with the option, which must not make it acceptable either.
mi_coqc_fails Evil -merge-inductives
mi_says "Universe inconsistency" "a universe inconsistency"
