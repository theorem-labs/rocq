#!/usr/bin/env bash

# Two template-polymorphic blocks that are identical word for word: they merge.
# The template data -- the context, the conclusion's sort, the per-parameter
# sorts and the defaults -- is part of what has to agree, so this is the test
# that [equal_template] passes a real pair, not only that it rejects one
# (misc/merge_inductives_neg_template).
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_template

mi_coqc Spec -merge-inductives
mi_coqc Agent -merge-inductives
mi_coqc Checker -merge-inductives

mi_rocqchk -merge-inductives MergeTest.Checker
