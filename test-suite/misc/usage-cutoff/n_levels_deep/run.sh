#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "n_levels_deep" (issue list item 3
# of 15). Depends on: D1 (comp_transitive_deps / the full transitive-closure
# fix). EXPECTED TO FAIL until commit comp_transitive_deps/Dvo_iface lands.
#
# Generalizes "two_level_false"/"b1_two_levels_export" beyond depth 2: a
# chain of 5 libraries, L1 (bottom, declares f) through L5 (top, re-exports
# L1..L4 and proves `b : f = 1`), with L5 four levels removed from f's
# declaration. D1's induction argument (#841, "Why this is complete, not
# just deeper") claims every transitively required library is checked
# directly against its own current state, not inferred through an
# intermediate's say-so, so this must scale to depth N, not just N=2. This
# test is the check that it actually does.
#
# Assertion: after changing f at the bottom of the chain and rebuilding
# L1..L4 (leaving L5.vo stale), a fresh compile of Top (which Requires L5
# and exploits the stale `b : f = 1` for a closed proof of False) MUST be
# refused once D1 lands.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/L1.v "$D"/L2.v "$D"/L3.v "$D"/L4.v "$D"/L5.v "$D"/Top.v "$WORK"/

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

for f in L1 L2 L3 L4 L5; do
  build "$f.v" >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build $f.v (BEFORE): $(cat "$WORK/setup.log")"
done

# AFTER: f := 2. Rebuild L1..L4 ONLY -- L5.vo is left stale, 4 levels removed
# from the change.
printf 'Definition f := 2.\n' > "$WORK/L1.v"
for f in L1 L2 L3 L4; do
  build "$f.v" >>"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD $f.v (AFTER) failed unexpectedly: $(cat "$WORK/rebuild.log")"
done

if out=$(build Top.v 2>&1); then
  echo "$out" >&2
  uc_fail "Top compiled against the stale L5.vo after a 4-level-down change to f -- closed proof of False with no axioms."
fi
uc_ok "Top was refused against the stale L5.vo: $(echo "$out" | tail -1)"
