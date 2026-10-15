#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 4, test "g7mod" (new,
# issuecomment-6189398514/round-5 issuecomment-6189455137). The round-4
# reviewer's own repro: the shadowed name lives in a library whose OWN
# top-level structure also contains a nested `Module`, which forces the
# kernel's own `iface_table_of_struct` to return `None` for the WHOLE
# library (the function's documented catch-all: any non-CONSTANT/
# non-INDUCTIVE top-level field zeroes the entire per-declaration table,
# not just that one field). X declares a plain `f := 1` AND an unrelated
# nested `Module Internal`, so X's own `iface_table` is `None` even
# though `f` itself is an ordinary flat constant.
#
# Same X/A/B/C shape as `g7_shadowing_refused`: B does
# `Require Import X A.` and proves `b : f = 1 := eq_refl`
# (f resolves to X.f, since A has no f yet); A is rebuilt to ADD a
# colliding `Definition f := 2.`.
#
# KNOWN OPEN GAP, not closed by this round's fix (CutoffG7b,
# binary-equivalence-taiga#841): G7 round 5's `closure_table` mechanism
# (kernel/safe_typing.ml, `flatten_closure`/`closure_subset_ok`) can only
# ever record a name that lives in a library whose OWN `iface_table` is
# `Some` -- a library with `iface_table = None` (X, here) contributes
# NOTHING to the per-id closure table at all, so `f`'s existence INSIDE X
# is invisible to the shadow check from the start; the SEPARATE
# `closure_none_digest` only catches X's OWN content changing or being
# added/removed, never a DIFFERENT library (A) later adding a name that
# happens to collide with one hidden inside X. See
# `kernel/safe_typing.ml`'s own doc comment on `flatten_closure`
# (the paragraph starting "A library whose OWN [iface_table] is [None]")
# for the full argument, and its "Tried and reverted" paragraph for why
# the obvious cheap fix (treat ANY addition anywhere as a refusal
# whenever a None-iface library is anywhere in the closure) was tried,
# built, and found to be UNSOUND in practice: the implicit prelude itself
# contributes at least one None-iface library to EVERY ordinary compile,
# so that fix regressed the entire feature (`unused_addition_still_reused`,
# `coqchk_strict_rejects_what_loader_accepts`, `g7_shadowing_refused`),
# not just this narrow case. Closing this residual gap for real needs
# enumerating names hidden inside a None-iface library's own structure,
# which `iface_table_of_struct`'s fallback deliberately does not attempt
# -- out of scope for this round, same risk class as the still-open
# G8/D1 gap (a dev-loop signal that can lie about what a fresh compile
# would do, never a path to an unsound ACCEPT at grading time, since
# grading always recompiles from source).
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v (has a nested Module, iface=None): $(cat "$WORK/setup.log")"
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
# X's None-iface table. Rebuild A ONLY -- B.vo (and C.vo) are left stale.
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, adds colliding f) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  uc_fail "EXPECTED TO FAIL (known residual gap, binary-equivalence-taiga#841 CutoffG7b, documented in kernel/safe_typing.ml's flatten_closure doc comment): coqc C.v WRONGLY reused B.vo after A added a declaration (f) colliding with X's OWN f, which is invisible to the closure table because X's iface_table is None (a nested Module anywhere in X's top level zeroes the WHOLE table, not just the module's own entry). A fresh compile of B against the same new A fails (confirmed above). Either this gap has been closed (re-check the doc comment / this test) or this fixture no longer reproduces it: $c_out"
fi
uc_ok "UNEXPECTED: reuse was refused (the residual gap may have been closed elsewhere): $(echo "$c_out" | grep -m1 'Inconsistent assumptions')"
