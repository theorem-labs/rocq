#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 4, test "g7mod" (new,
# issuecomment-6189398514/round-5 issuecomment-6189455137). The round-4
# reviewer's own repro: the shadowed name lives in a library whose OWN
# top-level structure also contains a nested `Module`. X declares a plain
# `f := 1` AND an unrelated nested `Module Internal`.
#
# Round 5 (CutoffG7b) left this OPEN: `iface_table_of_struct` bailed the
# WHOLE library to `None` the moment it saw ANY nested module anywhere in
# the file, hiding `f` from the G7 shadow check even though `f` itself is
# an ordinary flat top-level constant.
#
# Round 7 closes it: `iface_entries_of_sfb`/`iface_table_of_struct`
# (kernel/safe_typing.ml) now RECURSE into a nested module/module type's
# own expanded signature, collecting its `SFBconst`/`SFBmind` entries by
# their bare `Id.t` the same way a top-level one would be -- so `X`'s own
# `f` is tracked in the closure table regardless of the unrelated
# `Module Internal` sitting next to it in the same file.
#
# Same X/A/B/C shape as `g7_shadowing_refused`: B does
# `Require Import X A.` and proves `b : f = 1 := eq_refl`
# (f resolves to X.f, since A has no f yet); A is rebuilt to ADD a
# colliding `Definition f := 2.`.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v (has a nested Module): $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, f resolves to X.f): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

# Sanity: a FRESH compile of B against the AFTER-shadowing A really does fail.
cp "$D/A_after.v" "$WORK/A_fresh_check.v"
( cd "$WORK" && uc_coqc -Q . "" A_fresh_check.v ) >"$WORK/agent-standalone.log" 2>&1 \
  || uc_fail "SETUP: A_after.v (the shadowing addition) failed to compile standalone: $(cat "$WORK/agent-standalone.log")"
rm -f "$WORK"/A_fresh_check.*
cp "$D/B.v" "$WORK/B_fresh_check.v"
sed -i 's/Require Import X A\./Require Import X. Require Import A_after./' "$WORK/B_fresh_check.v" 2>/dev/null
cp "$D/A_after.v" "$WORK/A_after.v"
( cd "$WORK" && uc_coqc -Q . "" A_after.v ) >"$WORK/shadow-check.log" 2>&1 \
  || uc_fail "SETUP: could not build A_after.v as A_after for the fresh-shadow sanity check: $(cat "$WORK/shadow-check.log")"
fresh_out=$(cd "$WORK" && uc_coqc -Q . "" B_fresh_check.v 2>&1)
fresh_rc=$?
if [ "$fresh_rc" -eq 0 ]; then
  echo "$fresh_out" >&2
  uc_fail "SANITY: a fresh compile of B against the shadowing A succeeded -- this fixture does not actually exercise a name-shadowing hazard, nothing to test."
fi
rm -f "$WORK"/B_fresh_check.* "$WORK"/A_after.*

# AFTER: A grows a declaration that collides with a name hidden inside
# X's nested module's OWN file (X.f itself is top-level, but X also
# contains an unrelated nested Module). Rebuild A ONLY -- B.vo (and
# C.vo) are left stale.
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, adds colliding f) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after A added a declaration (f) colliding with X.f -- a fresh compile of B against the same new A fails (confirmed above), so this reuse is wrong. binary-equivalence-taiga#841 round 7 was supposed to close this via kernel/safe_typing.ml's recursive iface_entries_of_sfb; check that fix is still in place."
fi
echo "$c_out" | grep -q 'Inconsistent assumptions over module' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with the expected inconsistent-assumptions message -- got: $c_out"

uc_ok "colliding addition (f) correctly refused ($(echo "$c_out" | grep -m1 'Inconsistent assumptions'))"
