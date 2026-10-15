#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "vos_then_real_all" (issue list item
# 5 of 15). Depends on: D5 (cutoff_rocq.py forwards -vos/-vok/-vio/-beautify
# straight to the real binary with NO stamp interaction at all). Should
# PASS once D5 lands.
#
# rocq#10's deep review, Major M2, reproduced through a real coq_makefile
# Makefile: M.v is built once (a real .vo, stamp written). M.v is then
# edited to add a new declaration, `make vos` is run (a FAST, unsafe -vos
# pass -- NOT a real .vo), and then `make real-all` is run. Before the fix,
# the -vos pass was treated as an ordinary compile and WROTE a stamp
# matching the EDITED source even though the old, stale .vo was never
# touched; the following `make real-all` then saw a matching stamp and
# wrongly REUSED the stale .vo, so `after_marker` was silently missing.
#
# Assertion: after `make vos` then `make real-all`, the final .vo MUST
# reflect the edited source (after_marker present), built via a genuine
# REBUILD (the stats log must say REBUILD, not REUSED, since -vos must
# never have written a stamp for `make real-all` to wrongly match against).
. ../lib.sh

D=$(pwd)
WORK=$(mktemp -d "${TMPDIR:-/tmp}/usage-cutoff-vos.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

cp "$D/M_before.v" "$WORK/M.v"
printf -- '-Q . ""\nM.v\n' > "$WORK/_CoqProject"
( cd "$WORK" && "$UC_ROCQ" makefile -f _CoqProject -o Makefile ) >/dev/null

export CUTOFF_REAL_ROCQ="$UC_ROCQ"
export CUTOFF_AGENT_INTERACTIVE=1
STATS_LOG="$WORK/cutoff-stats.log"

mk() { ( cd "$WORK" && make -f Makefile "$@" ROCQ="python3 $UC_DRIVER" CUTOFF_STATS_LOG="$STATS_LOG" ); }

# Initial real build.
rm -f "$STATS_LOG"
mk real-all >"$WORK/build1.log" 2>&1 || uc_fail "initial 'make real-all' failed: $(cat "$WORK/build1.log")"
[ -f "$WORK/M.vo" ] || uc_fail "initial build did not produce M.vo"

# Edit, then `make vos`.
cp "$D/M_after.v" "$WORK/M.v"
rm -f "$STATS_LOG"
mk vos >"$WORK/vos.log" 2>&1 || uc_fail "'make vos' failed: $(cat "$WORK/vos.log")"
if [ -f "$STATS_LOG" ] && [ -s "$STATS_LOG" ]; then
  echo "--- unexpected stats log content after 'make vos':" >&2
  cat "$STATS_LOG" >&2
  uc_fail "'make vos' wrote to the cutoff stats log -- it must bypass the driver's stamp logic entirely (D5), not just happen to skip reuse."
fi

# Now the real build.
rm -f "$STATS_LOG"
mk real-all >"$WORK/build2.log" 2>&1 || uc_fail "'make real-all' after 'make vos' failed: $(cat "$WORK/build2.log")"

uc_assert_contains "$STATS_LOG" $'^REBUILD\tM\\.v' "the real-all pass after 'make vos' must REBUILD M.v (no valid stamp exists), not REUSE the stale pre-edit .vo"

check_out=$(cd "$WORK" && printf 'Print after_marker.\n' | "$COQBIN"rocq repl -batch -Q . "" -require-import M 2>&1)
echo "$check_out" | grep -q 'after_marker = 2' \
  || uc_fail "final M.vo does not reflect the post-'make vos' edit (after_marker missing/wrong) -- the stale pre-edit .vo was reused. Output: $check_out"

uc_ok "'make vos' wrote no stamp, and the following 'make real-all' correctly REBUILT M.vo to include after_marker."
