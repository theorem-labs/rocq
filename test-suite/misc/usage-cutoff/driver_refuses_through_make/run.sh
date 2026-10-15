#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "driver_refuses_through_make"
# (issue list item 14 of 15). Depends on: D1 (the full transitive-closure
# fix), routed through D5's driver and a REAL coq_makefile Makefile.
# EXPECTED TO FAIL until commit comp_transitive_deps/Dvo_iface lands.
#
# BugFinderRedTeamV2 M5/M6: every other test in this suite drives either
# raw coqc (tests 1-4/11-13/15) or checks a reuse decision only where reuse
# IS correct (tests 6/9/12). Nothing exercises "the driver asks the
# kernel, the kernel correctly refuses, the driver correctly forwards that
# refusal into a real rebuild" through an actual `make` invocation -- so a
# driver bug that hardcodes or inverts the REUSED/REBUILD decision (always
# claims REUSED regardless of what the kernel says) would pass every other
# test, including positive control #12 (which it would in fact satisfy
# MORE reliably under such a bug).
#
# X/A/B/C (the same shape as "two_level_false"), built and then driven
# through two real `make real-all` passes with ROCQ=cutoff_rocq.py. B
# declares `b := f` (no type assertion pinned to the old value, so a
# GENUINE rebuild succeeds cleanly and simply picks up the new value --
# unlike the exploit fixtures in tests 1-3, this test's point is the
# REBUILD/REUSED bookkeeping itself, not another closed-False repro).
#
# Assertion: after changing f at the bottom and rebuilding through `make`,
# the stats log MUST record REBUILD (never REUSED) for every file
# downstream of the change (A, B and C all transitively depend on X), and
# the final build's value for `result` must reflect the POST-edit world
# (2), not a stale snapshot (1).
. ../lib.sh

D=$(pwd)
WORK=$(mktemp -d "${TMPDIR:-/tmp}/usage-cutoff-refuse.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

cp "$D/X.v" "$D/A.v" "$D/B.v" "$D/C.v" "$WORK/"
printf -- '-Q . ""\nX.v\nA.v\nB.v\nC.v\n' > "$WORK/_CoqProject"
( cd "$WORK" && "$UC_ROCQ" makefile -f _CoqProject -o Makefile ) >/dev/null

export CUTOFF_REAL_ROCQ="$UC_ROCQ"
export CUTOFF_AGENT_INTERACTIVE=1
STATS_LOG="$WORK/cutoff-stats.log"
mk() { ( cd "$WORK" && make -f Makefile "$@" ROCQ="python3 $UC_DRIVER" CUTOFF_STATS_LOG="$STATS_LOG" ); }

rm -f "$STATS_LOG"
mk real-all >"$WORK/build1.log" 2>&1 || uc_fail "initial build (f := 1) failed: $(cat "$WORK/build1.log")"

cp "$D/X_after.v" "$WORK/X.v"
rm -f "$STATS_LOG"
if ! mk real-all >"$WORK/build2.log" 2>&1; then
  echo "--- build2.log:" >&2
  cat "$WORK/build2.log" >&2
  echo "--- stats log:" >&2
  cat "$STATS_LOG" >&2 2>/dev/null
  uc_fail "'make real-all' failed after changing f -- a genuine rebuild of B/C (no stale type dependency) should succeed once D1 lands."
fi

for f in A B C; do
  uc_assert_not_contains "$STATS_LOG" $'^REUSED\t'"$f"'\.v' "$f.v must NOT be REUSED after a change to f (it is downstream of the change)"
  uc_assert_contains "$STATS_LOG" $'^REBUILD\t'"$f"'\.v' "$f.v must show a REBUILD entry after a change to f"
done

result_out=$(cd "$WORK" && printf 'Print result.\n' | "$COQBIN"rocq repl -batch -Q . "" -require-import C 2>&1)
echo "$result_out" | grep -q 'result = 2' \
  || uc_fail "C.result does not reflect the post-edit value of f (expected 2) -- a stale B/C was used somewhere in the chain. Output: $result_out"

uc_ok "every file downstream of the change to f was genuinely REBUILT (never REUSED), and the final value reflects the post-edit world."
