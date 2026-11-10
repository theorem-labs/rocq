#!/usr/bin/env bash

# The shape every grader checker file has: it names the statement library's
# inductive DIRECTLY (`Definition agent_weight : Spec.Dup.sev -> nat :=
# Agent.Proof.weight.`), not only through constants.
#
# Such a .vo is written in its own names, as it must be, so the name it
# carries for the statement library's type is whatever that library was
# called -- and which of two merged copies keeps its name depends on the
# order they are loaded in, which is not the same for rocq c and for
# rocqchk. The check therefore has to be done on a body that names the
# merges the environment already made, not on the body as written out.
#
# Each -norec order below is a different load order, and all of them must
# accept. Without the option the same run must be refused, and an agent
# copy with one constructor argument more must be refused at compile time.
set -eu

. misc/merge_inductives_common.bash

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cp -r misc/merge_inductives_checker_direct/. "$d/"

Q="-Q $d/Spec Spec -Q $d/Agent Agent -Q $d/Checker Checker"
QB="-Q $d/Spec Spec -Q $d/AgentBad Agent -Q $d/Checker Checker"

mi_c () { $coqc -merge-inductives "$@" > "$d/last.log" 2>&1 \
            || mi_fail "$* was refused"; }
mi_c_fails () {
  set +e; $coqc "$@" > "$d/last.log" 2>&1; mi_status=$?; set -e
  [ "$mi_status" != 0 ] || mi_fail "$* was accepted"
  mi_no_anomaly "$*"
}
chk () { "$BIN"rocqchk $Q ${mi_chk_extra:-} "$@" > "$d/last.log" 2>&1 \
           || { echo "FAILED: rocqchk $* was refused"; cat "$d/last.log"; exit 1; }; }
chk_fails () {
  set +e; "$BIN"rocqchk $Q ${mi_chk_extra:-} "$@" > "$d/last.log" 2>&1; mi_status=$?; set -e
  [ "$mi_status" != 0 ] || mi_fail "rocqchk $* was accepted"
  mi_no_anomaly "rocqchk $*"
}

mi_c $Q "$d/Spec/Dup.v"
mi_c $Q "$d/Agent/Dup.v"
mi_c $Q "$d/Agent/Proof.v"
mi_c $Q "$d/Checker/Checker.v"

# Every load order accepts.
chk -merge-inductives Checker.Checker
chk -merge-inductives -norec Agent.Proof -norec Agent.Dup -norec Checker.Checker
chk -merge-inductives -norec Spec.Dup -norec Agent.Dup -norec Agent.Proof -norec Checker.Checker
chk -merge-inductives -norec Checker.Checker -norec Agent.Proof -norec Agent.Dup -norec Spec.Dup

# Without the option, the same .vo files are refused.
chk_fails Checker.Checker

# An agent copy that differs must not merge: one constructor takes one
# argument more, and the checker file is refused at compile time.
rm -f "$d"/*/*.vo "$d"/*/*.glob
mi_c $Q "$d/Spec/Dup.v"
mi_c $QB "$d/AgentBad/Dup.v"
mi_c $QB "$d/AgentBad/Proof.v"
set +e
$coqc -merge-inductives $QB "$d/Checker/Checker.v" > "$d/last.log" 2>&1
mi_status=$?
set -e
[ "$mi_status" != 0 ] || mi_fail "Checker.v was accepted against the bad agent copy"
mi_no_anomaly "Checker.v"
mi_says sev "sev"
