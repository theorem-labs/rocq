#!/bin/bash
# binary-equivalence-taiga#841 D6, test "stale_vo_version_rejected" (issue
# list item 8 of 15). Carried over from v1's
# dev/usage-cutoff/test_stale_vo_version.sh "unchanged" per #841's own
# instruction ("still correct, still needed") -- but with the hardcoded
# /rocq/... paths rocq#10's deep review flagged (m6) replaced by REQUIRED
# environment variables, no machine-specific defaults.
#
# NOT wired into `make -C test-suite`'s misc/usage-cutoff subsystem: unlike
# every other case in test-suite/misc/usage-cutoff/, this one fundamentally
# needs TWO separately installed Rocq toolchains (a pre-fork/pre-format-
# change STOCK compiler, and the fork UNDER TEST), which the test-suite's
# single-$BIN harness has no way to express. Run this directly, with both
# toolchains built and both environment variables set.
#
# Root cause: kernel/safe_typing.ml's library_info / vernac/library.ml's
# md_deps/library_deps widened from a (DirPath.t, vodigest) pair to a wider
# tuple (see #841 "D1"/"D3"/"D4"), but tools/configure/configure.ml's
# vo_magic was never bumped alongside it in v1. Rocq's own cross-version
# .vo check (lib/objFile.ml's Coq_config.vo_version comparison, raising the
# cleanly-handled Bad_version_number -- lib/system.ml's
# with_magic_number_check) therefore never fires on a .vo built by
# anything that doesn't understand the wider tuple -- any pre-fork Rocq,
# including the pinned stock toolchain this fork is forked from. Requiring
# such a stale .vo unmarshals its old-shape dependency record as the
# fork's wider tuple type and dereferences whatever bytes happen to follow
# it as the phantom extra field(s): undefined behavior, observed as
# SIGSEGV on a real vendor tree where some dependencies were already
# compiled by the stock switch before the fork's mtime-driven `make` ever
# touched them.
#
# Fix: this fork's own vo_magic bump (see #841 "vo_magic": a fork-reserved
# range, e.g. +1000 over whatever commit 1 lands on, documented at the
# reservation site so a later bump on this branch doesn't re-collide with
# upstream's own small sequential increments), so the existing version
# check now actually distinguishes the two formats and a stale .vo is
# refused with a plain "bad version number" error -- the same failure
# class a genuinely-broken proof already produces -- instead of a crash.
#
# Required environment variables (no defaults -- m6 in rocq#10's deep
# review flagged v1's hardcoded /rocq/... paths specifically):
#   STOCK_COQC - a Rocq/coqc built from BEFORE this fork's tuple-widening
#                change (any pre-fork commit produces the old-shape
#                format).
#   ROCQC      - the fork coqc UNDER TEST.
#   OLD_ROCQC  - optional: a pre-FIX fork coqc (vo_magic still unbumped) to
#                demonstrate the segfault actually reproduces on this exact
#                fixture before the fix. Skipped if unset.
set -u

: "${STOCK_COQC:?set STOCK_COQC to a pre-fork coqc (produces the old, narrower dependency-tuple .vo format); no default is provided on purpose, see this script's header}"
: "${ROCQC:?set ROCQC to the fork coqc under test; no default is provided on purpose, see this script's header}"
OLD_ROCQC="${OLD_ROCQC:-}"

WORK="${WORK:-$(mktemp -d "${TMPDIR:-/tmp}/cutoff-stale-vo-test.XXXXXX")}"
trap 'rm -rf "$WORK"' EXIT

switch_env() {
  # Exports the env a coqc binary at $1 needs, derived from its own path
  # (two directories up from bin/coqc) so each binary under test runs
  # fully against its own switch -- a stale PATH/CAML_LD_LIBRARY_PATH left
  # over from a different switch in the calling shell has caused native
  # compilation to pick up another switch's mismatched .cmx files here.
  local prefix
  prefix="$(cd "$(dirname "$1")/.." && pwd)"
  export PATH="$prefix/bin:/usr/bin:/bin"
  export CAML_LD_LIBRARY_PATH="$prefix/lib/stublibs:$prefix/lib/ocaml/stublibs:$prefix/lib/ocaml"
  export OCAMLTOP_INCLUDE_PATH="$prefix/lib/toplevel"
}

rm -rf "$WORK" && mkdir -p "$WORK"
cat > "$WORK/A.v" <<'EOF'
Definition a := 1.
Lemma pf : a = 1.
Proof. reflexivity. Qed.
EOF
cat > "$WORK/B.v" <<'EOF'
Require Import A.
Definition b := a.
EOF

switch_env "$STOCK_COQC"
if ! "$STOCK_COQC" -native-compiler no -Q "$WORK" "" "$WORK/A.v" >"$WORK/stock-build.log" 2>&1; then
  echo "SETUP FAILED: could not build A.vo with STOCK_COQC=$STOCK_COQC"
  cat "$WORK/stock-build.log"
  exit 2
fi
echo "stale (pre-fork-format) A.vo built with $STOCK_COQC"

check_one() {
  local label=$1 bin=$2 out rc
  switch_env "$bin"
  out=$("$bin" -native-compiler no -Q "$WORK" "" "$WORK/B.v" 2>&1)
  rc=$?
  rm -f "$WORK/B.vo" "$WORK/B.glob" "$WORK/B.vos" "$WORK/B.vok"
  echo "-- $label ($bin): exit=$rc"
  echo "$out" | tail -5 | sed 's/^/     /'
  if [ "$rc" -gt 128 ]; then
    echo "-- $label: CRASHED (killed by signal $((rc - 128)))"
    return 1
  fi
  if echo "$out" | grep -qi "bad version number"; then
    echo "-- $label: clean version-mismatch error"
    return 0
  fi
  echo "-- $label: unexpected outcome (neither clean version error nor a crash)"
  return 2
}

status=0
if [ -n "$OLD_ROCQC" ]; then
  if check_one "BEFORE (pre-fix fork)" "$OLD_ROCQC"; then
    echo "UNEXPECTED: pre-fix fork did not reproduce the stale-.vo issue on this fixture -- OLD_ROCQC may not actually predate the vo_magic fix, or the fixture no longer exercises the bug."
    status=1
  else
    echo "confirmed: pre-fix fork reproduces the stale-.vo failure mode on this fixture (crash or ambiguous outcome)."
  fi
fi

if check_one "AFTER (fork under test)" "$ROCQC"; then
  echo "PASS: fork under test cleanly rejects the stale .vo with a version-mismatch error."
else
  echo "FAIL: fork under test did not cleanly reject the stale .vo (crashed, or gave an unexpected outcome)."
  status=1
fi

exit $status
