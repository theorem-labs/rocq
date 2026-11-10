# Shared helpers for the merge_inductives_* tests.
#
# -merge-inductives is opt-in: with it, each inductive block of a library being
# loaded is compared with the blocks already loaded, and a matching one is
# given the already-loaded copy's canonical name, so that two copies of the
# same type declared in libraries that do not know about each other become one
# type. These tests pin which copies match and which do not.
#
# This file is deliberately not named *.sh: the misc target runs every
# misc/*.sh as a test of its own (see the "misc:" rule in test-suite/Makefile).
# That rule exports $coqc (an "eval"-prefixed "rocq c" command line) and $BIN,
# and runs the script from the test-suite directory; it does not export a
# rocqchk command, so rocqchk is spelled "$BIN"rocqchk, as in
# misc/norec-validation-order.sh. A test passes by exiting 0.

# All libraries of this family are compiled under one logical root.
mi_root=MergeTest

mi_fail () {
  echo "FAILED: $*"
  if [ -f "$d/last.log" ]; then cat "$d/last.log"; fi
  exit 1
}

# mi_setup <source directory>...: copy the .v sources of each directory into a
# fresh scratch directory and leave its name in $d. Compiling in a scratch
# directory keeps the .vo files of the tests that compile the same sources with
# and without the option apart, and leaves the source tree clean.
mi_setup () {
  d=$(mktemp -d)
  trap 'rm -rf "$d"' EXIT
  local src
  for src in "$@"; do
    cp "$src"/*.v "$d/"
  done
}

# mi_coqc <library> [option...]: compile $d/<library>.v, which must succeed.
mi_coqc () {
  local base=$1; shift
  $coqc -R "$d" $mi_root "$@" "$d/$base.v" > "$d/last.log" 2>&1 \
    || mi_fail "$base.v was refused"
}

# mi_coqc_fails <library> [option...]: compile $d/<library>.v, which must be
# refused, and cleanly: a refusal that is an anomaly is a failure. The output
# is left in $d/last.log and the exit code in $mi_status.
mi_coqc_fails () {
  local base=$1; shift
  set +e
  $coqc -R "$d" $mi_root "$@" "$d/$base.v" > "$d/last.log" 2>&1
  mi_status=$?
  set -e
  [ "$mi_status" != 0 ] || mi_fail "$base.v was accepted"
  mi_no_anomaly "$base.v"
}

# mi_rocqchk <argument>...: check the named libraries, which must succeed.
mi_rocqchk () {
  "$BIN"rocqchk -R "$d" $mi_root "$@" > "$d/last.log" 2>&1 \
    || mi_fail "rocqchk $* was refused"
}

# mi_rocqchk_fails <argument>...: check the named libraries, which must be
# refused, and cleanly. Exit code in $mi_status, output in $d/last.log.
mi_rocqchk_fails () {
  set +e
  "$BIN"rocqchk -R "$d" $mi_root "$@" > "$d/last.log" 2>&1
  mi_status=$?
  set -e
  [ "$mi_status" != 0 ] || mi_fail "rocqchk $* accepted"
  mi_no_anomaly "rocqchk $*"
}

mi_no_anomaly () {
  ! grep -q 'Anomaly' "$d/last.log" || mi_fail "$1 failed with an anomaly"
}

# mi_says <pattern> <what>: the last refusal must be the expected one. The
# tests match on the kernel's and the elaborator's own wording, never on the
# line -merge-inductives-verbose prints.
mi_says () {
  grep -q "$1" "$d/last.log" || mi_fail "the refusal does not mention $2"
}

# mi_negative <source directory> [spec] [agent]: the shape every
# merge_inductives_neg_* test has. Agent.v differs from Spec.v in exactly one
# way, so the two blocks must not be merged: each library still compiles and
# checks on its own, and Checker.v, which typechecks only if the two copies
# became one type, is refused. Checker.v never produces a .vo, so what rocqchk
# is asked here is the other half: refusing the merge leaves both libraries
# valid.
mi_negative () {
  local dir=$1 spec=${2:-Spec} agent=${3:-Agent}
  mi_setup "$dir"
  mi_coqc "$spec" -merge-inductives
  mi_coqc "$agent" -merge-inductives
  mi_coqc_fails Checker -merge-inductives
  mi_rocqchk -merge-inductives "$mi_root.$spec" "$mi_root.$agent"
}
