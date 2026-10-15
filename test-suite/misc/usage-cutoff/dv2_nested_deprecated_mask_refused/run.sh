#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 8 (Lean round 7 review, "dv2"). Same
# bare-id masking bug as kd1/kd2 (see those fixtures' headers), reached
# through [Declaremods.G1Partition.vernac_iface] instead of the kernel
# [Safe_typing.iface_table]: X has a nested `M.foo` AND a top-level `foo`.
# B uses `X.M.foo` under `Set Warnings "+deprecated"`. X is rebuilt adding
# a `#[deprecated]` attribute to `M.foo` ONLY (top-level `foo` untouched).
# A fresh compile of B now errors (the deprecation warning promoted to an
# error); the SAME vernac_iface masking bug that made kd1/kd2 reachable
# also applied here, via [Declare]'s own CONSTANT cutoff classifier
# reading [Global.current_modpath ()] at [end_library] time (always the
# wrong, top-level path for a nested declaration) and the resulting
# bare-[Id.t]-keyed vernac_iface entries colliding. Round 8 fixes both:
# [Declare.constant_obj] now captures its own [ModPath.t] at declaration
# time, and vernac_iface entries are keyed by a qualified string derived
# from the (now correctly-scoped) [GlobRef.t], not a bare [Id.t].
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/X_before.v" "$WORK/X.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, M.foo not deprecated): $(cat "$WORK/setup.log")"

cp "$D/X_after.v" "$WORK/X.v"
build X.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD X (AFTER, M.foo deprecated) failed unexpectedly: $(cat "$WORK/rebuild.log")"

# Sanity: a fresh compile of B against the now-deprecated X really does
# fail under +deprecated.
rm -f "$WORK"/B_fresh_check.*
cp "$D/B.v" "$WORK/B_fresh_check.v"
fresh_out=$(cd "$WORK" && uc_coqc -Q . "" B_fresh_check.v 2>&1)
fresh_rc=$?
if [ "$fresh_rc" -eq 0 ]; then
  echo "$fresh_out" >&2
  uc_fail "SANITY: a fresh compile of B against the deprecated X succeeded -- this fixture does not actually exercise a deprecation hazard, nothing to test."
fi
echo "$fresh_out" | grep -qi deprecated \
  || uc_fail "SANITY: fresh B against deprecated X failed, but not with a deprecation message -- got: $fresh_out"
rm -f "$WORK"/B_fresh_check.*

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after X.M.foo became deprecated -- a fresh compile of B now errors under +deprecated (confirmed above), so this reuse is wrong."
fi
echo "$c_out" | grep -qi 'inconsistent assumptions' \
  || uc_fail "coqc C.v refused (exit $c_rc) but not with the expected inconsistent-assumptions message -- got: $c_out"

uc_ok "nested M.foo's new deprecation correctly refused ($(echo "$c_out" | grep -im1 'inconsistent assumptions'))"
