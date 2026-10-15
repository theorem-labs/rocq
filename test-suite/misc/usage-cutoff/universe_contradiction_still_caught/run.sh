#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "universe_contradiction_still_caught"
# (issue list item 11 of 15). Depends on: unaffected by D1 (still correct
# whichever way D1 lands), but FLIPPED by G2's fix (Review841): before G2,
# `comp_univs`/`comp_sorts` were outside both digests, so this scenario's
# opaque-proof-introduced universe constraint (`pose (U1 : U2)`) was
# accepted by the relaxed loader and only caught by rocqchk's independent
# re-verification. G2 adds an exact-equality `(comp_univs, comp_sorts)`
# digest to `dep_ok`'s relaxed branch (kernel/safe_typing.ml), so the SAME
# scenario is now refused at `coqc`/interactive-loader time already:
# `Require Import A B` while compiling C invokes
# vernac/library.ml's `intern_mandatory_library`, which rejects because
# B's recorded dependency on A carries a (comp_univs, comp_sorts) digest
# that no longer matches A_agent's live digest. Should PASS once G2 lands
# (and fails at the pre-G2 head, where the old test's "loader accepts"
# assertion was in fact the design's acknowledged gap G2 closes).
#
# U declares two universes; the reference A's opaque proof adds no extra
# constraint; B bakes in `U2 <= U1` against the reference A; the agent's
# A instead adds `U1 <= U2` (an opaque-proof-only constraint, via
# `pose (U1 : U2)`) -- together the two constraints are only mutually
# inconsistent once B.vo (compiled against the reference A) is combined
# with the rebuilt agent A. B.vo is kept (not rebuilt) when A is swapped.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/U.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_ref.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build U.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build U.v: $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (reference): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (against reference A): $(cat "$WORK/setup.log")"

# Sanity: the agent's A, with a constraint the OPPOSITE direction from B's,
# compiles fine standalone -- the constraint is only a problem once merged
# with B.
cp "$D/A_agent.v" "$WORK/A_fresh_check.v"
( cd "$WORK" && uc_coqc -Q . "" A_fresh_check.v ) >"$WORK/agent-standalone.log" 2>&1 \
  || uc_fail "agent's A (pose (U1 : U2)) failed to compile standalone: $(cat "$WORK/agent-standalone.log")"
rm -f "$WORK"/A_fresh_check.*

# Reuse scenario: agent's A replaces the reference A; B.vo is kept.
cp "$D/A_agent.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (agent) failed unexpectedly: $(cat "$WORK/rebuild.log")"

# The trust anchor (post-G2): the interactive loader itself must now
# refuse to load B.vo against the changed A -- not merely let rocqchk
# catch it later.
c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo against an A whose (comp_univs, comp_sorts) digest changed (pose (U1 : U2)) -- G2's fix is not being applied by dep_ok's relaxed branch."
fi
echo "$c_out" | grep -qi 'inconsistent assumptions' \
  || uc_fail "coqc C.v failed (exit $c_rc) but not with an inconsistent-assumptions error -- got: $c_out"

# Independent second confirmation: rocqchk over the actual merged object
# set also catches the universe contradiction on its own strict path
# (unaffected by G2 -- it never took the relaxed branch to begin with).
chk_out=$(cd "$WORK" && "$UC_ROCQCHK" -o -Q . "" -norec U -norec A -norec B 2>&1)
chk_rc=$?
if [ "$chk_rc" -eq 0 ]; then
  echo "$chk_out" >&2
  uc_fail "rocqchk accepted the merged U/A/B tree -- the universe contradiction (U1 <= U2 and U2 <= U1) was not caught."
fi
echo "$chk_out" | grep -qi 'Universe inconsistency' \
  || uc_fail "rocqchk rejected the merged tree (exit $chk_rc) but not with the specific 'Universe inconsistency' error -- the previous grep (-E 'universe|inconsisten') was non-discriminating: it also matches rocqchk's own '[intern .../universe_contradiction_still_caught/work/B.vo' progress lines, since the TEST DIRECTORY NAME itself contains 'universe' (binary-equivalence-taiga#841 Review841 round 2, R4). Got: $chk_out"

uc_ok "coqc C.v correctly refused the reuse ($(echo "$c_out" | grep -im1 'inconsistent assumptions')), and rocqchk independently confirmed the universe contradiction over U/A/B with the specific error: $(echo "$chk_out" | grep -i -m1 'Universe inconsistency')"
