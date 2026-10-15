#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 G1, test "g1_changed_statement_still_refused"
# (new, item 19). Depends on: G1.
#
# Confirms G1's exclusion of CONSTANT/INDUCTIVE from the exact-equality
# vernac objects digest did NOT accidentally weaken anything: a dependency
# whose declaration B actually USES changes its VALUE (p : I1 -> I2, same
# type, different content), and B's OWN cached .vo (proving p = I1) is left
# untouched while only A is rebuilt. A downstream file C requiring the STALE
# B.vo must be refused -- caught by the existing kernel-level comp_iface
# per-declaration digest (D1/D3), which G1 does not touch at all.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D/B.v" "$D/C.v" "$WORK/"

build() { ( cd "$WORK" && uc_coqc -Q . T "$1" ); }

cp "$D/A_orig.v" "$WORK/A.v"
build A.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, proving p = I1): $(cat "$WORK/setup.log")"

# AFTER: A's p changes value. Rebuild A ONLY -- B.vo is left exactly as it
# was, still claiming (and having proved) p = I1.
cp "$D/A_changed.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, p changed) failed unexpectedly: $(cat "$WORK/rebuild.log")"

if out=$(build C.v 2>&1); then
  echo "$out"
  uc_fail "C (requiring the STALE B.vo) was ACCEPTED after A's p -- which B's proof directly used -- changed value. This must be REFUSED; G1's exclusion must not weaken the existing per-declaration check."
fi
echo "$out" > "$WORK/refuse.log"

uc_assert_contains "$WORK/refuse.log" "inconsistent assumptions" \
  "C was refused, but not with the expected 'inconsistent assumptions' message"

uc_ok "C correctly refused the stale B.vo after A's directly-used declaration changed value: $(echo "$out" | tail -1)"
