#!/usr/bin/env bash

# merge_inductives_demo over a parameterised, Type-valued block: [wrap] takes a
# parameter, so the merge has to agree on parameters, on the constructor's type
# and on the template universes an [Inductive w (A : Type)] gets, not only on
# names. coqc compiles the three libraries with -merge-inductives and rocqchk
# recomputes the merge from the .vo files.
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_wrap

mi_coqc Spec -merge-inductives
mi_coqc Agent -merge-inductives
mi_coqc Checker -merge-inductives

mi_rocqchk -merge-inductives MergeTest.Checker
