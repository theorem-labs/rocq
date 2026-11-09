#!/usr/bin/env bash

# merge_inductives_leak through a module alias (review finding P1-1, route 2).
# Mid is compiled WITH the option and aliases the agent's library; a reader
# without the option must still see two types, and rocqchk must accept Mid
# either way.
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_leak_alias

mi_coqc Spec -merge-inductives
mi_coqc Agent -merge-inductives
mi_coqc Mid -merge-inductives

mi_rocqchk MergeTest.Mid
mi_rocqchk -merge-inductives MergeTest.Mid

mi_coqc_fails Evil
mi_says tree "tree"
