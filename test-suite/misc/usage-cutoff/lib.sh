# Shared helpers for binary-equivalence-taiga#841 D6 ("real tests") usage-
# cutoff regression tests. NOT itself a test: it has no run.sh, so the
# Makefile's `misc/usage-cutoff/*/run.sh` glob never picks this directory
# up. Sourced by each case's run.sh as `. ../lib.sh` after the top-level
# Makefile rule has already `cd`-ed into the case directory and exported
# BIN/COQBIN/COQPREFIX/coqc/coqchk (see test-suite/Makefile's
# "usage-cutoff" subsystem section).
#
# Every case here is a REAL, assertion-bearing test per rocq#10's Major-6 /
# binary-equivalence-taiga#841 finding 6: a property that doesn't hold MUST
# make run.sh exit non-zero, never merely print a mismatch and exit 0.

set -uo pipefail

export COQBIN="${COQBIN:-$BIN}"
export PATH="$COQBIN:$PATH"

# Repo root, derived from this file's own location (never hardcoded, unlike
# v1's dev/usage-cutoff scripts, which is exactly what finding 6/m6 flagged).
# test-suite/misc/usage-cutoff/lib.sh -> ../../.. is the repo root (misc ->
# test-suite -> repo root); the previous ../../../.. landed one level
# ABOVE the repo root, so UC_DRIVER/UC_ROCQ could never be found
# (binary-equivalence-taiga#841 Review841 D6 table, tests 5/6/9/14).
UC_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
UC_DRIVER="$UC_ROOT/dev/usage-cutoff/cutoff_rocq.py"
UC_ROCQ="${COQBIN}rocq"
UC_ROCQCHK="${COQBIN}rocqchk"

uc_fail() {
  echo "FAIL: $*" >&2
  exit 1
}

uc_ok() {
  echo "OK: $*"
}

# uc_assert_contains FILE PATTERN [MESSAGE] -- grep -q (basic regex), loud
# failure with the file's contents on mismatch.
uc_assert_contains() {
  local file=$1 pattern=$2 msg=${3:-"expected to find '$pattern' in $file"}
  if ! grep -q -- "$pattern" "$file" 2>/dev/null; then
    echo "--- $msg" >&2
    echo "--- actual contents of $file:" >&2
    cat "$file" >&2 2>/dev/null || echo "(file does not exist)" >&2
    uc_fail "$msg"
  fi
}

uc_assert_not_contains() {
  local file=$1 pattern=$2 msg=${3:-"did not expect to find '$pattern' in $file"}
  if grep -q -- "$pattern" "$file" 2>/dev/null; then
    echo "--- $msg" >&2
    echo "--- actual contents of $file:" >&2
    cat "$file" >&2
    uc_fail "$msg"
  fi
}

uc_assert_eq() {
  local actual=$1 expected=$2 msg=${3:-"expected '$expected', got '$actual'"}
  if [ "$actual" != "$expected" ]; then
    uc_fail "$msg"
  fi
}

# uc_coqc ARGS... -- invoke the fork's own `rocq c` directly (NOT the
# Makefile-exported `$coqc`, whose `-R prerequisite TestSuite` is relative
# to the test-suite root: every case here `cd`s into its own scratch
# directory first, where that relative path would resolve to a directory
# that doesn't exist).
uc_coqc() {
  "$UC_ROCQ" c "$@"
}

# uc_sha256 FILE
uc_sha256() {
  sha256sum "$1" | cut -d' ' -f1
}
