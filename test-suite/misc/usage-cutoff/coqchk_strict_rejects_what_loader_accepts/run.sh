#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test
# "coqchk_strict_rejects_what_loader_accepts" (issue list item 4 of 15).
# Depends on: D2 (coqchk's strict, relaxed-branch-absent import path) AND,
# as of this rewrite, G1 (the per-declaration subset layer) -- see
# "Precondition gate" below for why G1 turns out to be load-bearing here
# too, which the original design did not anticipate.
#
# Two earlier fixture candidates were tried and EMPIRICALLY RULED OUT
# while rewriting this test (binary-equivalence-taiga#841 Review841's own
# finding that the ORIGINAL fixture didn't discriminate D2 at all):
#   1. Review841's own "d2" control (A's Constraint strength weakens,
#      u < v -> u <= v; B doesn't use the constraint): worked BEFORE G2
#      landed, but G2's fix now digests (comp_univs, comp_sorts) into
#      `dep_ok`'s relaxed branch too, so the interactive loader now
#      refuses this exact edit as well -- both agree, no split.
#   2. An opaque (Qed) proof's SCRIPT changing while its type/universe
#      context/flags stay fixed (`reflexivity` -> `symmetry;reflexivity`,
#      guaranteed-different compiled terms, verified by sha256 on A.vo):
#      the interactive loader DOES accept this (as expected -- an opaque
#      term is excluded from the per-declaration interface digest by
#      design). But `rocqchk -norec` ALSO accepts it -- verified directly
#      (both `-norec A -norec Bf` and auto-admitting A as Bf's dependency
#      via `-norec Bf` alone). Root cause, found by reading
#      `checker/checkLibrary.ml`'s `intern_from_file`: coqchk's own
#      "digest" is `Safe_typing.Dvo_or_vi seg_md.hash` -- the hash of ONLY
#      the `library_seg` segment. The opaque proof table is a SEPARATE
#      segment (`seg_opaque`), read independently and NEVER folded into
#      that digest. So an opaque-term-only change is invisible to
#      coqchk's OWN notion of "digest" too -- there is no split here
#      either, and in fact this edit can NEVER produce one, regardless of
#      G1/G2's status, since coqchk structurally cannot see it.
#
# With those two ruled out, and with every OTHER observable edit to a
# dependency currently forced through an EXACT-equality check pre-G1
# (objects_digest for any libobject or declaration-set change; iface_table
# for any EXISTING declaration's type/universe-context/flags/transparent-
# value, since a library's recorded `comp_iface` snapshot covers every
# declaration that existed at compile time, not just the ones a specific
# dependent happened to reference; comp_univs/comp_sorts since G2;
# retroknowledge forces `comp_iface = None`, collapsing `dep_ok` to plain
# `digest_match` so the relaxed and strict checks become IDENTICAL, not a
# split), there is currently NO constructible edit where the interactive
# loader accepts a reuse that differs from what it was compiled against.
# G1 is what actually OPENS this acceptance window (the per-declaration
# subset layer specifically tolerates an unused ADDITION, same shape as
# "unused_addition_still_reused"/"dvo_iface_pass_through_to_subset") --
# until it lands, D2's backstop has nothing to discriminate FROM.
#
# Precondition gate, not a guess at behavior: build the SAME
# unused-addition shape "unused_addition_still_reused" uses. If the
# interactive loader still REFUSES it (G1 absent, matching the current
# head), fail loudly with that reason rather than fabricating a pass.
# Once G1 lands and the addition is accepted, run coqchk over the exact
# same on-disk tree (A rebuilt-with-addition, B.vo stale) and assert it
# refuses -- A's raw file digest changed (the addition shows up in
# `seg_md`, unlike an opaque term), so `check_required_strict`'s
# `digest_match` (the ONLY check coqchk's `import_strict` ever takes) must
# differ, independent of G1's new per-declaration tolerance.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_ref.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE): $(cat "$WORK/setup.log")"

cp "$D/A_helper.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, unused helper added) failed unexpectedly: $(cat "$WORK/rebuild.log")"

gate_out=$(build C.v 2>&1)
gate_rc=$?
if [ "$gate_rc" -ne 0 ]; then
  uc_fail "G1 (the per-declaration subset layer) has not landed yet -- an unused addition to A is still refused by the interactive loader ($(echo "$gate_out" | tail -1)), so there is currently NO edit the relaxed loader accepts that differs from what a dependent was compiled against. D2's backstop has nothing to discriminate from until G1 opens that acceptance window -- see this file's header for the two fixture candidates (comp_univs weakening, opaque-term change) ruled out by direct experiment. This is not a guess: 'unused_addition_still_reused' exercises the identical scenario and is expected to fail for the same reason."
fi

# G1 has landed: the relaxed loader just accepted an edit (A grew an
# unused declaration) that changed A's raw file digest. coqchk, handed
# the exact same on-disk tree, must never take that relaxed branch.
chk_out=$(cd "$WORK" && "$UC_ROCQCHK" -o -Q . "" -norec A -norec B 2>&1)
chk_rc=$?
if [ "$chk_rc" -eq 0 ]; then
  echo "$chk_out" >&2
  uc_fail "rocqchk -norec accepted a tree where A's raw digest changed (unused addition) -- D2's strict path is not being taken."
fi
echo "$chk_out" | grep -qi -E 'inconsisten|incons' \
  || uc_fail "rocqchk -norec rejected the tree (exit $chk_rc) but not with an inconsistent-assumptions error; got: $chk_out"
uc_ok "the relaxed loader accepted the reuse (G1), and rocqchk -norec independently rejected it: $(echo "$chk_out" | grep -i -m1 -E 'inconsisten|incons')"
