#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test
# "coqchk_strict_rejects_what_loader_accepts" (issue list item 4 of 15).
# Depends on: D2 (coqchk's strict, relaxed-branch-absent import path) ONLY.
#
# Rewritten for Review841 round 2 (issuecomment-6188182538, finding R3):
# the previous rewrite's premise -- "until G1 lands, no edit is accepted by
# the relaxed loader yet refused by coqchk" -- is FALSE. Review841's own
# "e8" experiment found a real split that exists TODAY, independent of G1:
#
#   A: `Definition g := 0.` -> `Definition g := 0.` + `Require Y.` (an
#   unused, no-op import of a trivially-compilable library Y, added to A).
#   B (`Require Import A.`) uses `g`.
#
# The `REQUIRE` leaf Y's require creates is Anticipate-dropped from A's
# exported-objects digest (so `objects_digest`/`iface`/`comp_univs` are all
# UNCHANGED for A), but A's own `comp_deps` array gains a new entry for Y,
# which changes A's whole-library SEGMENT digest -- the raw file digest
# `check_required_strict`'s `digest_match` compares (and, pre-commit-1, the
# same raw digest the interactive loader's fast path falls back on too)
# -- even though nothing in the per-declaration/objects-digest/univs-digest
# surface the relaxed loader's SUBSET check actually looks at changed. So
# the relaxed loader accepts the reuse via its subset fallback (dep_ok's
# (b) branch), while rocqchk's `import_strict` -- digest equality ONLY,
# `check_required_strict`'s only check, never evaluating (b) at all --
# correctly refuses it. This IS a real, present-day D2 regression test;
# it does not need G1.
#
# Two earlier fixture candidates were tried and EMPIRICALLY RULED OUT in an
# earlier rewrite of this test (kept here for the record -- see git history
# for the fixtures, now removed since e8 replaces both):
#   1. Review841's own "d2" control (A's Constraint strength weakens,
#      u < v -> u <= v; B doesn't use the constraint): worked BEFORE G2
#      landed, but G2's fix now digests (comp_univs, comp_sorts) into
#      `dep_ok`'s relaxed branch too, so the interactive loader now
#      refuses this exact edit as well -- both agree, no split.
#   2. An opaque (Qed) proof's SCRIPT changing while its type/universe
#      context/flags stay fixed: the interactive loader DOES accept this,
#      but `rocqchk -norec` ALSO accepts it -- coqchk's own "digest" never
#      folds the opaque proof segment in, so this edit is invisible to
#      BOTH sides and can never produce a split.
#
# Verified directly on 619ecf0c7a (see README.md's row for this test for
# the actual run output): `coqc C.v` (reusing the stale B.vo after A grows
# `Require Y.`) exits 0; `rocqchk -norec A -norec B` on the exact same
# on-disk tree exits non-zero with `User error: Inconsistent assumptions
# over module A .`.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/Y.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build Y.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build Y.v: $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, uses g): $(cat "$WORK/setup.log")"

# AFTER: A gains an unused `Require Y.` -- no declaration B used changed,
# but A's whole-library segment digest (comp_deps grew an entry) did.
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, unused Require Y added) failed unexpectedly: $(cat "$WORK/rebuild.log")"

# The relaxed loader: must ACCEPT the reuse of the stale B.vo (this is the
# acceptance window D2's strict path exists to be a backstop against).
c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -ne 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v was refused reusing B.vo after A grew an unused Require Y -- the relaxed loader's subset layer did not accept this edit as expected (e8), so this test cannot demonstrate a split against coqchk. Got: $c_out"
fi

# The trust anchor: coqchk's strict path, which never evaluates the subset
# condition at all, must independently refuse the exact same on-disk tree.
chk_out=$(cd "$WORK" && "$UC_ROCQCHK" -o -Q . "" -norec A -norec B 2>&1)
chk_rc=$?
if [ "$chk_rc" -eq 0 ]; then
  echo "$chk_out" >&2
  uc_fail "rocqchk -norec accepted a tree where A's raw segment digest changed (unused Require Y) -- D2's strict path is not being taken, or is not actually strict."
fi
echo "$chk_out" | grep -qi 'Inconsistent assumptions' \
  || uc_fail "rocqchk -norec rejected the tree (exit $chk_rc) but not with an inconsistent-assumptions error; got: $chk_out"

uc_ok "the relaxed loader accepted reusing B.vo after A grew an unused Require Y (coqc C.v exit 0), and rocqchk -norec independently rejected the same on-disk tree: $(echo "$chk_out" | grep -i -m1 'Inconsistent assumptions')"
