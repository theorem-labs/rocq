#!/usr/bin/env bash

# The P0 paradox in the grader's shape: the libraries the merge needs arrive
# unchecked. The universe equalities a merge rests on must be recorded on
# that path too, so that the file which would close False is refused.
#
# What is NOT here, and why: the review's last arm asks for rocqchk to refuse
# Evil2.vo under -norec. No such .vo can exist once this is fixed -- Mid
# records the equality, so every compile of Evil2 is refused and nothing is
# written. The arm would need a .vo produced by a binary without the fix.
# What is checked instead is that no compile of it succeeds, in the shape
# where the merged libraries are the unchecked ones.
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_grader_shape_p0

mi_coqc Spec -merge-inductives
mi_coqc Agent -merge-inductives
mi_coqc Mid -merge-inductives

# Mid.vo carries the equality, so the paradox file is refused either way.
mi_coqc_fails Evil
mi_says "Universe inconsistency" "a universe inconsistency"
mi_coqc_fails Evil -merge-inductives
mi_says "Universe inconsistency" "a universe inconsistency"
mi_coqc_fails Hurkens
mi_says "Universe inconsistency" "a universe inconsistency"

# And the merge itself still happens when the merged libraries are the
# unchecked ones: only Mid is listed, so Spec and Agent are both loaded as
# its dependencies, unchecked. Mid's own check is then refused -- it is the
# shape the review calls P2, a library whose own terms name a merged
# inductive -- so both halves are asserted: that a merge happened with the
# spec side unchecked, and that the refusal is a clean one.
mi_rocqchk_fails -merge-inductives-verbose -o -norec "$mi_root.Mid"
mi_says 'Merged inductive' "a merge with the spec library unchecked"
