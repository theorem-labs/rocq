#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "vm_compute_cast_refused_on_body_change"
# (Lean attack-shape port, lean-build-perf#6, assignment part 2b). NEGATIVE
# counterpart to vm_compute_cast_safe_under_reuse/. Here `f` is a
# TRANSPARENT `Definition` (not opaque), so `vm_compute` genuinely unfolds
# it: B's `Eval vm_compute in (f + 0)` fully reduces `f` into the cached
# value of `b`. A changes f's BODY (`3` -> `4`) in a way that changes what
# `vm_compute A.f` reduces to -- `canon_const_body` (kernel/safe_typing.ml)
# maps a transparent `Def` to `CBDef <the actual term>`, so
# `iface_digest_of_const` genuinely differs for `f` between the two
# versions, and the per-declaration fallback must refuse reuse of B
# regardless of whether the whole-library digest would also have caught it
# (it would, here, since literally nothing else about A is byte-identical
# either -- this test exists to confirm the DIRECTION is correct, same
# convention as univ_constraint_drop_refused/, not to isolate one specific
# digest component in isolation).
#
# Verified while writing this fixture: a FRESH (non-reused) compile of B.v
# against each A variant produces a DIFFERENT value for b (3 vs 4) --
# confirming the fixture genuinely depends on f's changed body, not a false
# positive.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build A.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE, f := 3): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (against A-before): $(cat "$WORK/setup.log")"

# Sanity: fresh builds of a standalone vm_compute probe against each A
# variant produce DIFFERENT results -- the fixture genuinely exercises
# f's changed body, not a false positive that would refuse for an
# unrelated reason. (B.v itself prints nothing, so the probe is a
# separate file, not B.v renamed.)
write_probe() {
  printf 'Require Import A.\nDefinition b_check : nat := Eval vm_compute in (f + 0).\nPrint b_check.\n' > "$WORK/probe.v"
}
write_probe
before_val=$(build probe.v 2>&1 | grep -oE 'b_check = [0-9]+' || true)
rm -f "$WORK"/probe.*
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, f := 4) failed unexpectedly: $(cat "$WORK/rebuild.log")"
write_probe
after_val=$(build probe.v 2>&1 | grep -oE 'b_check = [0-9]+' || true)
rm -f "$WORK"/probe.*
uc_assert_eq "$before_val" "b_check = 3" "fresh probe against A_before should vm_compute f+0 to 3, got '$before_val' -- fixture is broken"
uc_assert_eq "$after_val" "b_check = 4" "fresh probe against A_after should vm_compute f+0 to 4, got '$after_val' -- fixture doesn't actually depend on f's changed body"

# A is now at A_after (f := 4) on disk; B.vo (above) was compiled against
# A_before (f := 3) and is left stale.
c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing the stale B.vo against an A whose transparent f's body changed (3 -> 4) -- the per-declaration digest is not catching a transparent body change a vm_compute cast depends on."
fi
echo "$c_out" | grep -qi 'inconsistent assumptions' \
  || uc_fail "coqc C.v failed (exit $c_rc) but not with an inconsistent-assumptions error -- got: $c_out"

uc_ok "A changing transparent f's body (3 -> 4, vm_compute'd in B) correctly refused reuse of the stale B.vo: $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
