#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "univ_constraint_drop_refused" (new,
# added for Review841's G2). Depends on: G2's fix -- kernel/safe_typing.ml
# now digests each dependency's own `(comp_univs, comp_sorts)` pair into
# `req_univs_digest`/`comp_univs_digest`, and `dep_ok`'s relaxed-acceptance
# branch requires EXACT equality on it. Should PASS now that G2 has landed.
#
# Review841's own "e4" experiment, lifted directly: A declares three
# universes and a constraint `u < v` (a bare `Universe`/`Constraint`
# command pushes straight to the global graph with no libobject at all, so
# neither the per-declaration iface_table nor the exported-objects digest
# ever see it -- G2's whole finding). B's type genuinely needs the
# constraint (`Type@{max(v,w)} := Type@{u}` requires `u < v`, since
# `u+1 <= max(v,w)` only holds if `u < v` lets `u+1 <= v <= max(v,w)`).
# A is then rebuilt WITHOUT the constraint; B.vo is left stale.
#
# Verified empirically while writing this fixture: a *fresh* rebuild of
# B.v against the constraint-dropped A genuinely fails ("universe
# inconsistency: Cannot enforce u+1 <= max(v, w)"), confirming the fixture
# encodes a real dependency on the dropped constraint, not a false
# positive. Before G2, reusing the stale B.vo against the rebuilt A
# incorrectly accepted (exit 0) despite that real inconsistency.
#
# Assertion: a fresh compile of C (`Require Import B.`), reusing the stale
# B.vo against the constraint-dropped A, MUST be refused with an
# inconsistent-assumptions error -- never silently accepted.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build A.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE, with constraint u < v): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, against A-with-constraint): $(cat "$WORK/setup.log")"

# AFTER: A drops the constraint entirely. Rebuild A ONLY -- B.vo (compiled
# against the constrained A) is left stale on disk.
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, constraint dropped) failed unexpectedly: $(cat "$WORK/rebuild.log")"

# Sanity: a fresh compile of B against the NOW-constraint-dropped A.vo on
# disk genuinely fails -- the fixture isn't a false positive.
cp "$D/B.v" "$WORK/B_fresh_check.v"
if ( cd "$WORK" && uc_coqc -Q . "" B_fresh_check.v ) >"$WORK/fresh-check.log" 2>&1; then
  uc_fail "a fresh compile of B.v succeeded even without A's Constraint u < v -- the fixture doesn't actually exercise the dropped constraint (test is broken)."
fi
rm -f "$WORK"/B_fresh_check.*

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo against an A whose Constraint u < v was dropped -- G2's (comp_univs, comp_sorts) digest check is not being applied by dep_ok's relaxed branch."
fi
echo "$c_out" | grep -qi 'inconsistent assumptions' \
  || uc_fail "coqc C.v failed (exit $c_rc) but not with an inconsistent-assumptions error -- got: $c_out"

uc_ok "A dropping Constraint u < v correctly refused reuse of the stale B.vo: $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
