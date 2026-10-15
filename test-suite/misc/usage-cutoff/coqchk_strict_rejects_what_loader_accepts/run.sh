#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test
# "coqchk_strict_rejects_what_loader_accepts" (issue list item 4 of 15).
# Depends on: D2 (coqchk's strict, relaxed-branch-absent import path). Must
# PASS regardless of D1's status -- this is the point of the test: it is
# D2's own control, independent of whether the Blocker (D1's concern) is
# open or closed.
#
# Setup is the Blocker's own tree (Z/A/Bf, the same shape "two_level_false"
# and "b1_two_levels_export" use): Z declares z; A re-exports it; Bf
# requires only A and proves `b : z = 1`. Z then changes and A is rebuilt,
# Bf.vo left stale -- precisely the state in which rocq#10's deep review
# found the INTERACTIVE loader (pre-D1) would accept Bf.vo. This test
# never drives that exploit through the interactive loader at all (see
# "two_level_false" for that): it only asks whether `rocqchk`, handed the
# exact same stale-Bf-plus-fresh-A-and-Z tree, independently catches the
# inconsistency via its own strict, digest-only import path (D2) --
# `checker/safe_checking.ml` must never reach the relaxed fallback, so this
# must hold no matter what the interactive loader does with Cf (see
# rocq#10 deep review, Major M1, and #841 "D2").
#
# Assertion: `rocqchk -norec` over {Z, A, Bf} (A, Z fresh; Bf stale) MUST
# reject with an inconsistent-assumptions error, not accept it.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/Z.v "$D"/A.v "$D"/Bf.v "$WORK"/

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build Z.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build Z.v (BEFORE): $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build Bf.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build Bf.v (BEFORE): $(cat "$WORK/setup.log")"

# AFTER: z := 2. Rebuild Z and A ONLY -- Bf.vo is left stale. Note we never
# attempt to compile anything that Requires Bf here: the point is to check
# coqchk directly against this exact on-disk state, not to route the
# exploit through the interactive loader first.
printf 'Definition z := 2.\n' > "$WORK/Z.v"
build Z.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD Z (AFTER) failed unexpectedly: $(cat "$WORK/rebuild.log")"
build A.v >>"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER) failed unexpectedly: $(cat "$WORK/rebuild.log")"

chk_out=$(cd "$WORK" && "$UC_ROCQCHK" -o -Q . "" -norec Z -norec A -norec Bf 2>&1)
chk_rc=$?
if [ "$chk_rc" -eq 0 ]; then
  echo "$chk_out" >&2
  uc_fail "rocqchk -norec accepted a tree where Bf.vo is stale against a changed Z two levels down -- D2's strict path is not being taken."
fi
echo "$chk_out" | grep -qi -E 'inconsisten|incons' \
  || uc_fail "rocqchk -norec rejected the tree (exit $chk_rc) but not with an inconsistent-assumptions error; got: $chk_out"
uc_ok "rocqchk -norec correctly rejected the stale-Bf tree: $(echo "$chk_out" | grep -i -m1 -E 'inconsisten|incons')"
