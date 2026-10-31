# Shared by the misc/library-label* and misc/vo-format tests. Sourced from
# the test-suite directory, before a test cds into its own.
#
# TOOL: the rocq-library-label of the build under test, from
# $LIBRARY_LABEL, the installed tool ($BIN) or the dune build's
# executable; exits 1 when there is none.
# check WHAT CONDITION...: run CONDITION, print PASS or FAIL WHAT, and set
# fail=1 on a failure.
# has TEXT PATTERN: PATTERN matches a line of TEXT.
TOOL=${LIBRARY_LABEL:-}
for t in "${BIN}rocq-library-label" "$PWD/../_build/default/checker/library_label.exe"; do
  if [ -z "$TOOL" ] && [ -x "$t" ]; then TOOL=$t; fi
done
if [ -z "$TOOL" ]; then
  echo "rocq-library-label not found: dune build checker/library_label.exe, or set LIBRARY_LABEL"
  exit 1
fi

check() { # check WHAT CONDITION...
  local what=$1; shift
  if "$@"; then echo "PASS $what"; else echo "FAIL $what"; fail=1; fi
}
has() { grep -q -- "$2" <<< "$1"; }
