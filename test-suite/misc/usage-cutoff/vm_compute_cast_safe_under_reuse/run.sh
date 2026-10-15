#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "vm_compute_cast_safe_under_reuse"
# (Lean attack-shape port, lean-build-perf#6, assignment part 2a). A
# dependent B's compiled proof term BAKES IN a `vm_compute` cast against a
# dependency A's declaration `f` (`Eval vm_compute in (f 3 + 0)`, stored
# literally in B.vo's term for `b`). `kernel/nativeconv.ml`'s
# `native_conv_gen` recompiles fresh code from the CURRENT in-memory term
# on every call and never unfolds an opaque/`Undef` constant under any
# circumstances (#841's own "Can executed code diverge from the digest?"
# analysis) -- `vm_compute`'s own reduction machinery has the identical
# opacity-respecting property (it is the mechanism `native_conv_gen` falls
# back to with native disabled, `kernel/nativeconv.ml:196-200`), so a
# vm_compute cast against an OPAQUE `f` can never observe `f`'s body
# regardless of whether reuse is granted: the cast stays identically stuck
# on `f 3` either way, so a reused B.vo cannot have silently diverged from
# what a fresh compile would produce.
#
# Two phases, because the literal shape in #841's analysis (`f` goes
# Admitted -> Qed) runs straight into a KNOWN, SEPARATE, already-documented
# gap (Review841 G1, not yet landed on this branch -- see tests 6, 9, 12 in
# this same suite) before it ever reaches the vm_compute question at all:
# `register_constant` (vernac/declare.ml) stores `cst_kind` inside the
# CONSTANT libobject for EVERY constant, Admitted vs Qed always changes it
# (`IsAssumption Conjectural` vs `IsProof`/`IsDefinition` depending on the
# opening command), and that libobject is part of the library's
# exact-equality `objects_digest` (D4) -- so ANY Admitted->Qed edit
# anywhere in a dependency is refused today, regardless of what a
# dependent's proof does or doesn't do with the changed declaration. This
# is sound (over-conservative, never unsafe) and is not a new,
# vm_compute-specific finding: it is the SAME root cause as tests 6/9/12.
#
# Phase 1 (does not touch cst_kind, demonstrates the vm_compute-safety
# property on the mechanism AS IT STANDS TODAY, no G1 dependency): `f` is
# declared via `Definition f (n : nat) : nat. Proof. ... Qed.` in BOTH
# versions -- opaque the whole time, cst_kind stays IsDefinition/IsProof
# throughout -- with a DIFFERENT proof term between A_before/A_after
# (`exact (n + 1)` vs `exact (n + 2 - 1)`), so `canon_const_body`
# (kernel/safe_typing.ml) collapses both to the SAME `CBNoBody` marker:
# the per-declaration digest for `f` is identical across the edit, and
# nothing else in A changed, so this edit is accepted TODAY, unconditional
# on G1. MUST currently REUSE B.vo, and `rocqchk -norec` must confirm the
# reused tree is actually sound (not merely that the interactive loader
# didn't crash).
#
# Phase 2 (the literal #841 shape: Admitted -> Qed): included for
# completeness per the attack-shape port, asserting the property the
# design is EXPECTED to deliver once G1 lands. Currently refused for the
# G1 reason above, NOT because of any vm_compute-specific defect --
# documented, not silently skipped, matching this suite's existing
# convention for tests 6/9/12.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK/phase1" "$WORK/phase2"

build() { ( cd "$1" && uc_coqc -Q . "" "$2" ); }

# ---------------------------------------------------------------------
# Phase 1: Qed -> Qed, different proof term, opaque throughout (no G1
# dependency). MUST reuse, and the reused tree MUST be rocqchk-sound.
# ---------------------------------------------------------------------
P1="$WORK/phase1"
cp "$D"/B.v "$D"/C.v "$P1"/
cp "$D/phase1_A_before.v" "$P1/A.v"

build "$P1" A.v >"$P1/setup.log" 2>&1 || uc_fail "phase1 SETUP: could not build A.v (BEFORE, Qed): $(cat "$P1/setup.log")"
build "$P1" B.v >>"$P1/setup.log" 2>&1 || uc_fail "phase1 SETUP: could not build B.v (against A-before): $(cat "$P1/setup.log")"

cp "$D/phase1_A_after.v" "$P1/A.v"
build "$P1" A.v >"$P1/rebuild.log" 2>&1 || uc_fail "phase1 REBUILD A (AFTER, different Qed proof term) failed unexpectedly: $(cat "$P1/rebuild.log")"

p1_out=$(build "$P1" C.v 2>&1)
p1_rc=$?
if [ "$p1_rc" -ne 0 ]; then
  echo "$p1_out" >&2
  uc_fail "phase1: coqc C.v was REFUSED reusing B.vo after a Qed->Qed proof-term-only change to the vm_compute'd declaration f -- the per-declaration digest is treating an opaque body change as observable, which it must not (canon_const_body should have collapsed both to CBNoBody): $p1_out"
fi
echo "$p1_out" | grep -q '^b =' \
  || uc_fail "phase1: coqc C.v exited 0 but did not print b's value as expected -- harness is broken: $p1_out"

( cd "$P1" && "$UC_ROCQCHK" -Q . "" -norec A -norec B ) >"$P1/rocqchk.log" 2>&1 \
  || uc_fail "phase1: rocqchk -norec A B rejected the reused tree -- the interactive loader accepted something the strict checker does not consider sound: $(cat "$P1/rocqchk.log")"
uc_assert_contains "$P1/rocqchk.log" "Modules were successfully checked" \
  "phase1: rocqchk did not report success even though it exited 0"

uc_ok "phase1: a Qed->Qed proof-term change to f (opaque, vm_compute'd in B) correctly reused B.vo, confirmed rocqchk-sound"

# ---------------------------------------------------------------------
# Phase 2: Admitted -> Qed, the literal #841 shape. Expected to currently
# FAIL (refused) for the pre-existing G1 reason documented above, not
# landed on this branch -- same status as tests 6/9/12 in this suite.
# ---------------------------------------------------------------------
P2="$WORK/phase2"
cp "$D"/B.v "$D"/C.v "$P2"/
cp "$D/phase2_A_before.v" "$P2/A.v"

build "$P2" A.v >"$P2/setup.log" 2>&1 || uc_fail "phase2 SETUP: could not build A.v (BEFORE, Admitted): $(cat "$P2/setup.log")"
build "$P2" B.v >>"$P2/setup.log" 2>&1 || uc_fail "phase2 SETUP: could not build B.v (against A-before): $(cat "$P2/setup.log")"

cp "$D/phase2_A_after.v" "$P2/A.v"
build "$P2" A.v >"$P2/rebuild.log" 2>&1 || uc_fail "phase2 REBUILD A (AFTER, Qed) failed unexpectedly: $(cat "$P2/rebuild.log")"

p2_out=$(build "$P2" C.v 2>&1)
p2_rc=$?
if [ "$p2_rc" -ne 0 ]; then
  echo "$p2_out" >&2
  uc_fail "phase2 (EXPECTED until Review841 G1 lands -- see tests 6/9/12): coqc C.v refused reusing B.vo after f's Admitted->Qed edit. This is the pre-existing cst_kind/objects_digest gap, not a vm_compute-specific defect -- see this file's header. Observed: $p2_out"
fi
echo "$p2_out" | grep -q '^b =' \
  || uc_fail "phase2: coqc C.v exited 0 but did not print b's value as expected -- harness is broken: $p2_out"

( cd "$P2" && "$UC_ROCQCHK" -Q . "" -norec A -norec B ) >"$P2/rocqchk.log" 2>&1 \
  || uc_fail "phase2: rocqchk -norec A B rejected the reused tree: $(cat "$P2/rocqchk.log")"

uc_ok "phase2: f's Admitted->Qed edit (vm_compute'd in B) correctly reused B.vo once G1 lands, confirmed rocqchk-sound"
