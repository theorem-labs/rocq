#!/usr/bin/env bash

# The option is opt-in, and a .vo written with it on carries no merged name.
#
# These are merge_inductives_demo's sources, on purpose: the only difference
# between that test and this one is the option, so the two cannot drift apart.
#
# Without the option, the two copies stay two types: each library compiles,
# and Checker.v, which asks for the agent's theorem under the spec's
# statement, is refused. Then the three libraries are compiled again with the
# option, and a rocqchk without it is given the .vo files that merging
# produced: it sees what it would have seen had the option never existed, so
# it refuses Checker with a type error.
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_demo

mi_coqc Spec
mi_coqc Agent
mi_coqc_fails Checker
# The refusal is the one the two copies of [tree] cause, not some other error.
mi_says 'tree' 'the two copies of the inductive'

rm -f "$d"/*.vo "$d"/*.vok "$d"/*.vos "$d"/*.glob

mi_coqc Spec -merge-inductives
mi_coqc Agent -merge-inductives
mi_coqc Checker -merge-inductives

mi_rocqchk_fails MergeTest.Checker
# The kernel's own wording for this refusal; the exit code is reported rather
# than pinned, so that a change of exit code is read in the log and not as a
# failure of the merge itself.
mi_says 'Type error' 'a type error'
echo "rocqchk without -merge-inductives refused MergeTest.Checker (exit $mi_status)"
