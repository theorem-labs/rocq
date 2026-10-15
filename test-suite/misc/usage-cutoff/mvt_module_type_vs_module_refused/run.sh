#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 12 (Main/reviewer, fixture
# "mvt"). X has `Module M. Module Type T. Parameter f : nat. End T. End
# M.` (a MODULE TYPE); W adds a top-level `Module T` (a MODULE, different
# kind). B seals `Module Q : T.` -- the literal `: T` seal NEVER falls
# back to a module (confirmed: every ModType-kind Modintern site skips
# the module lookup entirely), so a fresh compile always succeeds
# regardless of W's unrelated module T.
#
# Round 13 (ik1-ik4/ik6) made a NEW live MODULE-kind entry for a bare name
# also collide with a RECORDED MODULE-TYPE entry of the same name,
# one-directionally, to close Include's ModAny fallback. The mechanism
# cannot distinguish "this modtype was reached via Include" from "via a
# plain `: T` seal" (recording only tracks the NAME, not which syntactic
# site resolved it) -- so mvt is now a sound, accepted over-refusal too
# (P3), the explicit cost Main's round-13 ruling named. mvt2/mvt3 (the
# other direction, or same kind) are unaffected and still reuse.
. ../lib.sh
D=$(pwd); WORK="$D/work"; rm -rf "$WORK"; mkdir -p "$WORK"
cp "$D"/X.v "$D"/A.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/W0.v" "$WORK/W.v"
build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }
build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP X: $(cat "$WORK/setup.log")"
build W.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP W (BEFORE): $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP A: $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP B (BEFORE): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP C (BEFORE): $(cat "$WORK/setup.log")"

cp "$D/W1.v" "$WORK/W.v"
build W.v >"$WORK/sanity.log" 2>&1 || uc_fail "rebuild W (AFTER): $(cat "$WORK/sanity.log")"
build A.v >>"$WORK/sanity.log" 2>&1 || uc_fail "rebuild A against W1: $(cat "$WORK/sanity.log")"
cp "$D/B.v" "$WORK/B_fresh_check.v"
fresh_out=$(cd "$WORK" && uc_coqc -Q . "" B_fresh_check.v 2>&1); fresh_rc=$?
[ "$fresh_rc" -eq 0 ] || { echo "$fresh_out" >&2; uc_fail "SANITY: fresh B failed -- expected to succeed (: T seal only ever resolves a module type)."; }
rm -f "$WORK"/B_fresh_check.*

cp "$D/W0.v" "$WORK/W.v"
build W.v >"$WORK/restore.log" 2>&1 || uc_fail "restore W: $(cat "$WORK/restore.log")"
build A.v >>"$WORK/restore.log" 2>&1 || uc_fail "restore A: $(cat "$WORK/restore.log")"
cp "$D/W1.v" "$WORK/W.v"
build W.v >"$WORK/rebuild.log" 2>&1 || uc_fail "rebuild W (AFTER): $(cat "$WORK/rebuild.log")"
build A.v >>"$WORK/rebuild.log" 2>&1 || uc_fail "rebuild A (AFTER): $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1); c_rc=$?
[ "$c_rc" -ne 0 ] || { echo "$c_out" >&2; uc_fail "coqc C.v reused B.vo -- expected a sound over-refusal after round 13 (mvt)."; }
echo "$c_out" | grep -qi 'inconsistent assumptions' || uc_fail "wrong refusal message: $c_out"
uc_ok "unrelated same-named Module T (different kind) correctly (if conservatively) refused post-round-13: $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
