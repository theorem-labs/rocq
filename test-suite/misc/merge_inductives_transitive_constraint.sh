#!/usr/bin/env bash

# The constraint check must hold for the third copy too.
#
# Spec and Agent declare the same block over their own universe u, both with
# `Constraint Set < u`, and merge. Agent's index entry then carries Agent's
# user name and Spec's canonical name. A third library C declares the block
# WITHOUT that constraint. The constraints of the library that DECLARED the
# candidate are the ones to compare -- Agent's, found under its user name --
# and against those C does not match, so C must not merge with either copy.
# Reading them off the canonical name instead made the comparison empty and
# let C in (review finding P1-2).
#
# CheckerOk is the control: the same third library WITH the constraint does
# merge, so the refusal below is the constraint's doing and not the shape's.
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_transitive_constraint

mi_coqc Spec -merge-inductives
mi_coqc Agent -merge-inductives
mi_coqc C -merge-inductives
mi_coqc Cok -merge-inductives

mi_coqc_fails Checker -merge-inductives
mi_says b "b"

mi_coqc CheckerOk -merge-inductives
mi_rocqchk -merge-inductives MergeTest.CheckerOk
