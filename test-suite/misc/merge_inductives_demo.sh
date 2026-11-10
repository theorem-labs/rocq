#!/usr/bin/env bash

# With -merge-inductives, two matching copies of an inductive type declared in
# libraries that do not know about each other are one type: Agent.v redeclares
# Spec.v's [color] and [tree] blocks word for word, so the agent's theorem has
# the spec's statement and Checker.v typechecks. rocqchk, given the same
# option, recomputes the merge from the .vo files and must reach the same
# verdict. misc/merge_inductives_off.sh compiles these very sources without the
# option and pins that Checker.v is then refused.
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_demo

mi_coqc Spec -merge-inductives
mi_coqc Agent -merge-inductives
mi_coqc Checker -merge-inductives

mi_rocqchk -merge-inductives MergeTest.Checker
