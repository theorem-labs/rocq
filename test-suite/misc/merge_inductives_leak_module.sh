#!/usr/bin/env bash

# merge_inductives_leak, through a Module, a Module Type and a functor.
#
# Mid.v is compiled WITH the option, so Agent.tree is merged into Spec.tree
# while it is compiled. None of that may reach Mid.vo: a reader that never
# compared the two copies must still see two types. The consumers are
# compiled WITHOUT the option and must both be refused on tree, and rocqchk
# must accept Mid with the option and without it.
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_leak_module

mi_coqc Spec -merge-inductives
mi_coqc Agent -merge-inductives
mi_coqc Mid -merge-inductives

# rocqchk accepts Mid either way: the .vo says nothing a merge is needed for.
mi_rocqchk MergeTest.Mid
mi_rocqchk -merge-inductives MergeTest.Mid

# Neither consumer may inherit the merge.
mi_coqc_fails EvilTop
mi_says tree "tree"
mi_coqc_fails EvilMod
mi_says tree "tree"
