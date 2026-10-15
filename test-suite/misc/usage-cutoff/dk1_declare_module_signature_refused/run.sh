#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 13 (reviewer fixture, same
# file source as ik1, issuecomment-6199895213). `Declare Module D : T`
# resolves T via the literal ModType kind, which never falls back to a
# module -- so a fresh compile always succeeds regardless of W's
# unrelated top-level Module T. The round-13 one-directional fix cannot
# tell this apart from ik1's Include-ModAny shadow: both produce the
# SAME recorded/live closure signature (T recorded as a module type from
# X, a NEW module T live from W), since the mechanism only tracks the
# NAME and its kind, never which syntactic site resolved it. This is now
# a sound, accepted over-refusal, the same category as mvt.
. ../lib.sh
NAME=$(basename "$(pwd)")
D=$(pwd); WORK="$D/work"; rm -rf "$WORK"; mkdir -p "$WORK"
cp "$D"/X.v "$D"/A.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/W0.v" "$WORK/W.v"
build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }
build X.v >"$WORK/setup.log" 2>&1 || uc_fail "$NAME SETUP X: $(cat "$WORK/setup.log")"
build W.v >>"$WORK/setup.log" 2>&1 || uc_fail "$NAME SETUP W (BEFORE): $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "$NAME SETUP A: $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "$NAME SETUP B (BEFORE): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "$NAME SETUP C (BEFORE): $(cat "$WORK/setup.log")"

cp "$D/W1.v" "$WORK/W.v"
build W.v >"$WORK/sanity.log" 2>&1 || uc_fail "$NAME rebuild W (AFTER): $(cat "$WORK/sanity.log")"
build A.v >>"$WORK/sanity.log" 2>&1 || uc_fail "$NAME rebuild A against W1: $(cat "$WORK/sanity.log")"
cp "$D/B.v" "$WORK/B_fresh_check.v"
fresh_out=$(cd "$WORK" && uc_coqc -Q . "" B_fresh_check.v 2>&1); fresh_rc=$?
[ "$fresh_rc" -eq 0 ] || { echo "$fresh_out" >&2; uc_fail "$NAME SANITY: fresh B failed -- expected to succeed (ModType-only lookup never falls back to a module); the over-refusal premise no longer holds."; }
rm -f "$WORK"/B_fresh_check.*

cp "$D/W0.v" "$WORK/W.v"
build W.v >"$WORK/restore.log" 2>&1 || uc_fail "$NAME restore W: $(cat "$WORK/restore.log")"
build A.v >>"$WORK/restore.log" 2>&1 || uc_fail "$NAME restore A: $(cat "$WORK/restore.log")"
cp "$D/W1.v" "$WORK/W.v"
build W.v >"$WORK/rebuild.log" 2>&1 || uc_fail "$NAME rebuild W (AFTER): $(cat "$WORK/rebuild.log")"
build A.v >>"$WORK/rebuild.log" 2>&1 || uc_fail "$NAME rebuild A (AFTER): $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1); c_rc=$?
[ "$c_rc" -ne 0 ] || { echo "$c_out" >&2; uc_fail "$NAME: coqc C.v reused B.vo -- expected a sound over-refusal post-round-13."; }
echo "$c_out" | grep -qi 'inconsistent assumptions' || uc_fail "$NAME wrong refusal message: $c_out"
uc_ok "$NAME correctly (if conservatively) refused post-round-13: $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
