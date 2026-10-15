#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "universe_contradiction_still_caught"
# (issue list item 11 of 15). Carried over from v1's run_universe.sh
# unchanged in substance ("confirmed still correct since comp_univs push in
# import is unconditional and untouched" -- not gated by D1-D5 at all), but
# with REAL assertions instead of v1's print-only script (fixing m2: v1's
# own coqchk step errored out, "Cannot find library"/an anomaly, making the
# printed trust-anchor evidence vacuous -- rocq#10 deep review, m2). Should
# PASS unconditionally (no design-decision dependency).
#
# The loader's interface digest deliberately does not track `comp_univs`
# (a library's whole-library monomorphic universe constraints), so an
# agent's opaque proof can add a universe constraint that contradicts one
# baked into a dependent compiled against the reference, WITHOUT the
# reused dependent being refused at load time: this case is expected to be
# ACCEPTED by the loader. The claim under test is that `rocqchk`, run over
# the actual merged object set regardless of how it got assembled, still
# catches the inconsistency (coqc's own `import` unconditionally pushes
# `comp_univs` with `~strict:true`, independent of which branch of the
# acceptance check passed).
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

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -ne 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v failed -- expected B.vo to be ACCEPTED here (comp_univs is deliberately outside the interface digest), so this is a false-REFUSE regression, not the universe check this test targets."
fi

# The trust anchor: rocqchk over the actual merged object set MUST catch
# the universe inconsistency, with a real, non-vacuous error (fixing m2).
chk_out=$(cd "$WORK" && "$UC_ROCQCHK" -o -Q . "" -norec U -norec A -norec B -norec C 2>&1)
chk_rc=$?
if [ "$chk_rc" -eq 0 ]; then
  echo "$chk_out" >&2
  uc_fail "rocqchk accepted the merged tree -- the universe contradiction (U1 <= U2 and U2 <= U1) was not caught."
fi
echo "$chk_out" | grep -qi -E 'universe|inconsisten' \
  || uc_fail "rocqchk rejected the merged tree (exit $chk_rc) but not with a universe/inconsistency error -- evidence is vacuous (m2): got: $chk_out"

uc_ok "B.vo was accepted for reuse (coqc C exit 0), and rocqchk independently caught the universe contradiction: $(echo "$chk_out" | grep -i -m1 -E 'universe|inconsisten')"
