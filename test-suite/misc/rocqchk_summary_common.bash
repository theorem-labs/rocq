# Shared helpers of the fork's misc tests that read the summary of
# rocqchk -o: rocqchk_admitted_summary.sh, rocqchk_sealed_axiom_summary.sh,
# rocqchk_ascribed_axiom_summary.sh, rocqchk_application_axiom_summary.sh,
# rocqchk_application_bound_summary.sh, rocqchk_functor_loop_summary.sh,
# rocqchk_walk_stop_summary.sh, rocqchk_cook.sh and
# rocqchk_primitive_type.sh. Each sources it with
#
#   . misc/rocqchk_summary_common.bash
#
# so that a change of the summary's format is made here for them. Upstream's
# assumptions-norec.sh keeps its own reader, as upstream wrote it.
#
# This file is deliberately not named *.sh: the misc target runs every
# misc/*.sh as a test of its own (see the "misc:" rule in test-suite/Makefile).
# That rule exports $BIN and runs the script from the test-suite directory;
# it does not export a rocqchk command, so rocqchk is spelled "$BIN"rocqchk.

# section <title> <log>: print one summary section of <log>: its
# "* <title>" line and the lines under it, up to the next "* " bullet. awk's
# index() takes the title literally, slashes and parentheses included.
section() { awk -v h="* $1" 'index($0, h) == 1 { p = 1; print; next } p && /^\* / { exit } p { print }' "$2"; }

# axioms <log> <argument>...: rocqchk -silent -o <argument>..., within a
# time limit, and its output in <log>. rocqchk must accept the library and
# print an Axioms section. Then print the names of that section, sorted. The
# caller keeps the standard output, so a failure is said on the standard
# error.
axioms () {
  local log=$1 R=0
  shift
  timeout 120 "$BIN"rocqchk -silent -o "$@" > "$log" 2>&1 || R=$?
  if [ "$R" = 124 ]; then
    echo "rocqchk -o did not end within 120 s: $*" >&2
    exit 1
  elif [ "$R" != 0 ]; then
    echo "rocqchk -o exited with $R: $*" >&2
    cat "$log" >&2
    exit 1
  elif ! grep -q '^\* Axioms' "$log"; then
    echo "rocqchk -o printed no Axioms section: $*" >&2
    cat "$log" >&2
    exit 1
  fi
  section 'Axioms' "$log" | sed -n 's/^    //p' | LC_ALL=C sort
}

# lists <log> <expected> <argument>...: axioms <log> <argument>..., whose
# names must be exactly <expected>, one per line, sorted as axioms sorts
# them. A failure is said on the standard error, with the log.
lists () {
  local log=$1 expected=$2 listed
  shift 2
  listed=$(axioms "$log" "$@") || exit 1
  if [ "$listed" != "$expected" ]; then
    echo "rocqchk -o did not list exactly the expected names: $*" >&2
    printf 'expected:\n%s\nlisted:\n%s\n' "$expected" "$listed" >&2
    cat "$log" >&2
    exit 1
  fi
}

# refusal <log> <argument>...: rocqchk -silent -o <argument>..., within a
# time limit, and its output in <log>. rocqchk must refuse to print a
# summary it could not complete (checker/mod_impl.ml): exit 1, no summary,
# and the error below. Then print what the error says after its first
# sentence. The caller keeps the standard output, so a failure is said on
# the standard error.
refusal () {
  local log=$1 R=0 line
  local error='Fatal Error: User error: The Axioms summary could not be completed: '
  shift
  timeout 120 "$BIN"rocqchk -silent -o "$@" > "$log" 2>&1 || R=$?
  if [ "$R" = 124 ]; then
    echo "rocqchk -o did not end within 120 s: $*" >&2
    exit 1
  fi
  line=$(grep -m 1 -F "$error" "$log") || line=
  if [ "$R" != 1 ] || [ -z "$line" ] || grep -q 'CONTEXT SUMMARY' "$log"; then
    echo "rocqchk -o exited with $R and did not refuse the summary: $*" >&2
    cat "$log" >&2
    exit 1
  fi
  printf '%s\n' "${line#"$error"}"
}
