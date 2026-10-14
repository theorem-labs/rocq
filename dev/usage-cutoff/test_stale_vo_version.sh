#!/bin/bash
# Regression test for the stale-.vo-format segfault.
#
# Root cause: kernel/safe_typing.ml's library_info / vernac/library.ml's
# md_deps-library_deps widened from a (DirPath.t, vodigest) pair to a
# (DirPath.t, vodigest, iface_table option) triple (commit 080476b61c,
# ROCQ-USAGE-CUTOFF.md Sec3/Sec6), but tools/configure/configure.ml's
# vo_magic was never bumped. Rocq's own cross-version .vo check (lib/
# objFile.ml's Coq_config.vo_version comparison, raising the cleanly-handled
# Bad_version_number -- lib/system.ml's with_magic_number_check) therefore
# never fires on a .vo built by anything that doesn't understand the wider
# tuple -- any pre-fork Rocq, including the pinned stock toolchain this fork
# is forked from. Requiring such a stale .vo unmarshals its 2-tuple
# dependency record as the fork's static 3-tuple type and dereferences
# whatever bytes happen to follow it as the phantom iface_table field:
# undefined behavior, observed as SIGSEGV. This is exactly what happened on
# the real Coturn tree: a tree with some dependencies already compiled by
# the stock switch (mtime newer than source, so `make` never re-ran them
# through the fork) segfaulted on every file that in turn required one of
# them -- 117/117 "initial build" attempts in the b/c replay arms
# (sami-rocqperf:/rocq/cutoff/replay-arm-{b,c}-initial.{log,stats},
# docs/build/VENDOR-FULL-TREE.md Sec(c) in binary-equivalence-taiga).
#
# Fix: bump vo_magic (tools/configure/configure.ml), so the existing
# version check now actually distinguishes the two formats and a stale .vo
# is refused with a plain "bad version number" error -- the same failure
# class a genuinely-broken proof already produces -- instead of a crash.
#
# Usage: ./test_stale_vo_version.sh
#   STOCK_COQC - a Rocq/coqc built from BEFORE the format change (any
#                pre-fork commit produces the old 2-tuple format; defaults
#                to the pinned stock switch on sami-rocqperf).
#   ROCQC      - the fork coqc UNDER TEST (defaults to the freshly built
#                cutoff opam switch on sami-rocqperf).
#   OLD_ROCQC  - optional: a pre-FIX fork coqc (vo_magic still unbumped) to
#                demonstrate the segfault actually reproduces on this exact
#                fixture before the fix. Skipped if unset.
set -u
WORK="${WORK:-/tmp/cutoff-stale-vo-test}"
STOCK_COQC="${STOCK_COQC:-/rocq/shared/opam-bet-b0adcb15/bin/coqc}"
ROCQC="${ROCQC:-/rocq/cutoff/opam-root/cutoff/bin/coqc}"
OLD_ROCQC="${OLD_ROCQC:-}"

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
    echo "WARNING: the pre-fix binary did NOT crash on this fixture -- the bug may not reproduce in this environment"
  else
    echo "BEFORE: confirmed -- the unfixed fork crashes on this exact fixture"
  fi
fi

if check_one "AFTER (fork under test)" "$ROCQC"; then
  echo "AFTER: PASS -- stale .vo rejected cleanly, no crash"
else
  echo "AFTER: FAIL -- the fork under test still mishandles a stale-format .vo"
  status=1
fi

exit $status
