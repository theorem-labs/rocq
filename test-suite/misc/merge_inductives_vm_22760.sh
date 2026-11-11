#!/usr/bin/env bash

# rocq#22760, an OPEN upstream VM bug, run over a merged type.
#
# The bug: for an inductive with more than 245-ish constructors the VM's
# symbolic branches collide with inner binders, so the VM's conversion
# accepts `f1 = f2` for two functions that differ. `coqc` accepts it, a
# check with the VM on accepts it, and a check with the VM off refuses it.
# It is upstream's, not this option's, and there is no fix yet.
#
# Why this test exists here: merge_inductives_vm_agree shows VM-on and
# VM-off giving the same verdict on every test of this family. That is NOT
# a reason to drop a VM-off pass. This file is a case where the two
# disagree for a reason that has nothing to do with merging, and a grade
# that trusts a VM-on check alone accepts `bad : False` through it.
#
# What is asserted: the known behaviour is unchanged by the option. With
# the option and without it, a VM-on check accepts and a VM-off check
# refuses -- the same four verdicts. The merge neither hides the bug nor
# widens it.
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_vm_22760

# -native-compiler no is not optional here: OCaml refuses more than 246
# non-constant constructors, so an install with the native compiler on by
# default cannot compile a 250-constructor inductive at all. Upstream's own
# copy of this reproducer is named d760_issue22760_nonative.v for the same
# reason. Without the flag this test passes only where native happens to be
# off, which is how it reached the branch.
mi_coqc Spec -native-compiler no -merge-inductives
mi_coqc Agent -native-compiler no -merge-inductives
mi_coqc Bad -native-compiler no -merge-inductives-verbose
# Without this the file could stop being about a merged type and nothing
# here would notice.
mi_says 'Merged inductive' "a merge of the two Big copies"

verdict () {
  local want=$1; shift
  set +e
  "$BIN"rocqchk -silent -R "$d" $mi_root "$@" > "$d/last.log" 2>&1
  local got=$?
  set -e
  [ "$got" = "$want" ] || mi_fail "rocqchk $* gave $got, expected $want"
  mi_no_anomaly "rocqchk $*"
}

for opt in "" "-merge-inductives"; do
  verdict 0   $opt -bytecode-compiler yes "$mi_root.Bad"
  verdict 129 $opt -bytecode-compiler no  "$mi_root.Bad"
done
