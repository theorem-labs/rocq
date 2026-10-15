#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "dvo_iface_pass_through_to_subset"
# (issue list item 13 of 15). Depends on: commit 1 ("sami/loc-free-
# identity", #861/Plan861InterfaceReuse) landing `Dvo_iface`, the new
# loc-free whole-library identity that becomes dep_ok's FAST-path condition
# (replacing the raw whole-library digest_match), plus D4's layering of the
# per-declaration iface_table/objects_digest strictly BELOW it. EXPECTED TO
# FAIL until commit comp_transitive_deps/Dvo_iface lands.
#
# Purpose (#841, "How the two layers compose"): a change that makes
# Dvo_iface differ (e.g. an unrelated added declaration) but whose effect
# on a SPECIFIC dependent is nil must still let that dependent's per-
# declaration subset layer accept reuse -- confirming the two layers
# actually compose, not merely that each works in isolation.
#
# Precondition gate, not a guess at behavior: `Dvo_iface` does not exist as
# an actual constructor/binding anywhere in kernel/checker/vernac sources
# on this branch yet (only as a forward-looking comment reference, e.g.
# kernel/safe_typing.ml's retroknowledge-disqualification note and
# vernac/declaremods.ml's Loc-normalization note, both added by the G1/G2
# slice -- a bare `grep -rq 'Dvo_iface'` false-positives on those comments
# and silently runs this test against the OLD fast path, failing for G1's
# unrelated reason instead of ever reaching the composition claim this
# test exists to check; reproduced while writing this fix). The gate below
# greps for `Dvo_iface of` (an OCaml constructor DEFINITION pattern), which
# only a real `vodigest`/digest-variant implementation would ever contain
# -- no comment in this tree phrases it that way. Until Dvo_iface lands,
# this test is intentionally UNABLE to distinguish itself from
# "unused_addition_still_reused" (which already covers the identical
# observable scenario via the old fast path) and fails loudly here rather
# than silently duplicating that test's assertions and claiming to have
# verified a composition claim it cannot yet observe.
set -uo pipefail
. ../lib.sh

if ! grep -rq 'Dvo_iface of' "$UC_ROOT/kernel" "$UC_ROOT/checker" "$UC_ROOT/vernac" 2>/dev/null; then
  uc_fail "Dvo_iface has not landed yet (commit 1, sami/loc-free-identity) -- dep_ok's fast path is still the raw whole-library digest, so this test cannot yet exercise the Dvo_iface/iface_table composition it is meant to check. See this file's header."
fi

# Dvo_iface has landed: run the actual composition check. An unrelated,
# unused addition to A must make Dvo_iface differ (any real addition
# changes even a loc-free whole-library identity) while B -- which never
# used the new declaration -- is still accepted via the per-declaration
# subset layer underneath it.
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

before_hash=$(uc_sha256 "$WORK/B.vo")

cp "$D/A_helper.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, unused helper added) failed unexpectedly: $(cat "$WORK/rebuild.log")"

if ! out=$(build C.v 2>&1); then
  echo "$out" >&2
  uc_fail "C was refused once Dvo_iface differed (unused addition to A) -- the subset layer did not take over once the fast path failed."
fi

after_hash=$(uc_sha256 "$WORK/B.vo")
uc_assert_eq "$after_hash" "$before_hash" \
  "B.vo's bytes changed -- B was recompiled rather than accepted via the subset layer underneath a failing Dvo_iface fast path."

uc_ok "Dvo_iface differed (unused addition) but the subset layer still accepted B.vo unchanged: $(echo "$out" | tail -1)"
