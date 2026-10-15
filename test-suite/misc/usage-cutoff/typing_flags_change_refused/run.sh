#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "typing_flags_change_refused" (Lean
# attack-shape port, lean-build-perf#6, assignment part 1). Not in the
# original 17-test D6 list -- a new case closing the specific concern
# raised in #841's own "Can executed code diverge from the digest?"
# section: a typing-flags pragma (`Unset Guard Checking`/`Unset Positivity
# Checking`/`Unset Universe Checking`) set around one declaration inside a
# dependency must not let a dependent's stale `.vo` silently reuse.
#
# `const_typing_flags` is already a field of `iface_digest_of_const`
# (kernel/safe_typing.ml -- grep that file for the function to confirm the
# field list at whatever line it sits on today), so this scenario is
# EXPECTED to already be refused at this head, with no implementation
# change needed. The fixture: A declares `f`, a structurally-recursive
# Fixpoint that typechecks identically whether Guard Checking is on or
# off; its compiled `const_typing_flags.check_guarded` differs between
# A_before.v (flag on throughout) and A_after.v (temporarily off around
# just `f`, restored before end of file). B requires A and uses `f`; B.vo
# is left stale when A is rebuilt from A_before to A_after.
#
# Caveat, read before "fixing" this test to isolate one digest component:
# `Unset`/`Set Guard Checking` are themselves Goptions libobjects (any
# `Set`/`Unset` command goes through `Lib.add_leaf`, library/goptions.ml's
# `declare_option` -- confirmed by reading that file), so they also land
# in `Declaremods.library_objects` and change A's exact-equality objects
# digest (D4) on their own, independent of `const_typing_flags`. At this
# head (no #861 Loc-normalization hook, no G1 declaration-keyed split) that
# objects digest ALSO still changes on nearly any edit (object order/count,
# raw `cst_loc`), so this fixture cannot cleanly prove "ONLY the
# per-declaration path catches this and nothing else would" by shell
# assertions alone -- it proves the weaker, still load-bearing property:
# the combined mechanism does not silently accept the flag change, and
# `const_typing_flags` IS present in the formula that would need to agree
# for the per-declaration fallback branch to ever accept a mismatched `f`.
#
# Sanity checks (so this isn't a vacuous "always refuses" test): (1) an
# IDENTICAL rebuild of A (no edit at all) still lets C reuse B -- the
# harness can tell "same" from "different"; (2) a FRESH (non-reused) build
# of B.v against A_after succeeds -- the flag change doesn't accidentally
# break typechecking, so the refusal below is purely a reuse-safety
# decision, not a disguised type error.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build A.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE, Guard Checking on throughout): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, against A-before): $(cat "$WORK/setup.log")"

# Sanity (1): rebuild A from the SAME source (no edit) -- B.vo must still
# be reusable, confirming the test below isn't vacuously refusing every
# possible A rebuild regardless of content.
cp "$D/A_before.v" "$WORK/A.v"
build A.v >"$WORK/identical-rebuild.log" 2>&1 || uc_fail "REBUILD A (identical source) failed unexpectedly: $(cat "$WORK/identical-rebuild.log")"
identical_out=$(build C.v 2>&1)
identical_rc=$?
[ "$identical_rc" -eq 0 ] || uc_fail "coqc C.v failed (exit $identical_rc) after an IDENTICAL rebuild of A -- the harness itself is broken, this isn't the typing-flags property: $identical_out"

# AFTER: A changes ONLY `f`'s typing flags (Unset Guard Checking around its
# declaration, restored before end of file) -- same name, same type, same
# term. Rebuild A ONLY -- B.vo (compiled against the flags-on A) is left
# stale on disk.
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, Guard Checking off around f) failed unexpectedly: $(cat "$WORK/rebuild.log")"

# Sanity (2): a fresh (non-reused) compile of B against the flag-changed A
# genuinely succeeds -- the fixture isn't a disguised type error.
cp "$D/B.v" "$WORK/B_fresh_check.v"
if ! ( cd "$WORK" && uc_coqc -Q . "" B_fresh_check.v ) >"$WORK/fresh-check.log" 2>&1; then
  uc_fail "a FRESH compile of B.v against the flag-changed A failed -- the fixture doesn't actually isolate a flags-only change (test is broken): $(cat "$WORK/fresh-check.log")"
fi
rm -f "$WORK"/B_fresh_check.*

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing the stale B.vo against an A whose f had its Guard Checking typing flag changed -- const_typing_flags is not being enforced by dep_ok's relaxed branch."
fi
echo "$c_out" | grep -qi 'inconsistent assumptions' \
  || uc_fail "coqc C.v failed (exit $c_rc) but not with an inconsistent-assumptions error -- got: $c_out"

uc_ok "A changing f's Guard Checking typing flag correctly refused reuse of the stale B.vo: $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
