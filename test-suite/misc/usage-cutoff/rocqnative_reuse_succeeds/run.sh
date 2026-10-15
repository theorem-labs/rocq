#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "rocqnative_reuse_succeeds" (issue
# list item 6 of 15). Depends on: D3 (the shared dep_ok predicate, used by
# rocqnative's own intern_mandatory_library instead of a bare digest-only
# check). Should PASS once D3 lands.
#
# rocq#10's code-quality review, Major-1, reproduced through a real
# coq_makefile Makefile with native compilation ON: A goes Admitted->Qed
# (a transparent-to-the-interface change: both collapse to the same
# canonical "no body visible to a dependent" marker); B (`apply a`) is
# REUSED by the interactive loader. `tools/CoqMakefile.in` then
# unconditionally runs `rocqnative` (COQNATIVE) on B.vo too, even though it
# was reused, not recompiled. Before D3, rocqnative's own
# intern_mandatory_library used a digest-only check with no fallback at
# all (not a stale copy of the relaxed predicate -- simply missing it), so
# it rejected the legitimately-reused B.vo and `make` failed.
#
# Assertion (Major-1's repro, inverted): `make` must now exit 0 end to end,
# where v1 failed.
. ../lib.sh

D=$(pwd)
WORK=$(mktemp -d "${TMPDIR:-/tmp}/usage-cutoff-native.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

cp "$D/A_admitted.v" "$WORK/A.v"
cp "$D/B.v" "$WORK/B.v"
printf -- '-Q . ""\n-native-compiler yes\nA.v\nB.v\n' > "$WORK/_CoqProject"
( cd "$WORK" && "$UC_ROCQ" makefile -f _CoqProject -o Makefile ) >/dev/null

export CUTOFF_REAL_ROCQ="$UC_ROCQ"
export CUTOFF_AGENT_INTERACTIVE=1
STATS_LOG="$WORK/cutoff-stats.log"
mk() { ( cd "$WORK" && make -f Makefile "$@" ROCQ="python3 $UC_DRIVER" CUTOFF_STATS_LOG="$STATS_LOG" ); }

rm -f "$STATS_LOG"
mk real-all >"$WORK/build1.log" 2>&1 || uc_fail "initial native build (A Admitted, B) failed: $(cat "$WORK/build1.log")"

cp "$D/A_qed.v" "$WORK/A.v"
rm -f "$STATS_LOG"
if ! mk real-all >"$WORK/build2.log" 2>&1; then
  echo "--- build2.log:" >&2
  cat "$WORK/build2.log" >&2
  echo "--- stats log:" >&2
  cat "$STATS_LOG" >&2 2>/dev/null
  uc_fail "'make real-all' failed after an Admitted->Qed edit with native compilation on -- rocqnative likely rejected the reused B.vo (Major-1)."
fi

uc_assert_contains "$STATS_LOG" $'^REUSED\tB\\.v' "B.v should have been REUSED (not recompiled) after an Admitted->Qed edit to A"
uc_ok "native build succeeded end to end with B.vo reused after an Admitted->Qed edit to A."
