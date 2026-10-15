#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "reused_target_settles" (issue list
# item 9 of 15). Depends on: D5 (a REUSED file has its .vo/.glob mtimes
# touched forward, so a later `make` sees it as up to date instead of
# re-invoking the driver on it every time). EXPECTED TO FAIL until G1
# lands (not D1): the Admitted->Qed edit below changes the CONSTANT
# libobject's `cst_kind` (`IsAssumption Conjectural` -> `IsProof _`),
# which sits inside the exact-equality objects digest (`md_objects`)
# regardless of D1/D5's status -- Review841 G1. D5's own mtime-settling
# fix is independently correct; this test just can't observe a REUSED
# verdict for this specific edit until G1's per-declaration split lands.
#
# rocq#10's code-quality review, Major-5, reproduced: A goes Admitted->Qed,
# B (unchanged) is REUSED. Before D5, a REUSED verdict returned without
# updating any on-disk state make's own mtime-based dependency check looks
# at, so EVERY later `make` invocation re-ran the driver's own
# `coqtop -require` subprocess for B all over again, and `make -q` never
# reported up to date.
#
# Assertion: after the REUSED build, a second `make real-all` performs
# ZERO work (an empty stats log -- no coqtop -require subprocess spawned
# for anything), and `make -q real-all` exits 0 (reports up to date).
# EXPECTED TO FAIL until G1 lands (see header above).
. ../lib.sh

D=$(pwd)
WORK=$(mktemp -d "${TMPDIR:-/tmp}/usage-cutoff-settle.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

cp "$D/A_admitted.v" "$WORK/A.v"
cp "$D/B.v" "$WORK/B.v"
printf -- '-Q . ""\nA.v\nB.v\n' > "$WORK/_CoqProject"
( cd "$WORK" && "$UC_ROCQ" makefile -f _CoqProject -o Makefile ) >/dev/null

export CUTOFF_REAL_ROCQ="$UC_ROCQ"
export CUTOFF_AGENT_INTERACTIVE=1
STATS_LOG="$WORK/cutoff-stats.log"
mk() { ( cd "$WORK" && make -f Makefile "$@" ROCQ="python3 $UC_DRIVER" CUTOFF_STATS_LOG="$STATS_LOG" ); }

rm -f "$STATS_LOG"
mk real-all >"$WORK/build1.log" 2>&1 || uc_fail "initial build (A Admitted, B) failed: $(cat "$WORK/build1.log")"

# Edit A -> Qed; B must be REUSED (not changed on disk).
cp "$D/A_qed.v" "$WORK/A.v"
rm -f "$STATS_LOG"
mk real-all >"$WORK/build2.log" 2>&1 || uc_fail "build after Admitted->Qed edit failed: $(cat "$WORK/build2.log")"
uc_assert_contains "$STATS_LOG" $'^REUSED\tB\\.v' "B.v must be REUSED after the Admitted->Qed edit to A"

# A second, immediate `make real-all` with nothing changed must do
# NOTHING: make's own mtime check must already see both files as current,
# so the driver is never invoked for either one (an empty stats log).
rm -f "$STATS_LOG"
mk real-all >"$WORK/build3.log" 2>&1 || uc_fail "third 'make real-all' (nothing changed) failed: $(cat "$WORK/build3.log")"
if [ -f "$STATS_LOG" ] && [ -s "$STATS_LOG" ]; then
  echo "--- unexpected stats log content on the settled re-run:" >&2
  cat "$STATS_LOG" >&2
  uc_fail "a repeat 'make real-all' with nothing changed re-invoked the driver (REUSED target never settled -- make's own mtime check is still being fooled)."
fi

# `make -q` must independently agree nothing needs doing.
if ! mk -q real-all >"$WORK/mkq.log" 2>&1; then
  echo "$(cat "$WORK/mkq.log")" >&2
  uc_fail "'make -q real-all' reported work pending when the tree is fully settled."
fi

uc_ok "a second 'make real-all' performed zero work after the REUSED verdict, and 'make -q' reports up to date."
