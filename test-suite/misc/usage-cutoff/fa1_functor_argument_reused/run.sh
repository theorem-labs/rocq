#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 12/13 (reviewer session
# 01a1325a, issuecomment-6199895213): exact fixture files from the
# reviewer's own round-12 run against e5b54e224c, where this already
# reuses correctly (fresh B succeeds) -- a control for the opposite
# direction (module over module type) or a ModType-only lookup site,
# which never falls back to a module.
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
[ "$fresh_rc" -eq 0 ] || { echo "$fresh_out" >&2; uc_fail "$NAME SANITY: fresh B failed -- expected to succeed; the control premise no longer holds."; }
rm -f "$WORK"/B_fresh_check.*

cp "$D/W0.v" "$WORK/W.v"
build W.v >"$WORK/restore.log" 2>&1 || uc_fail "$NAME restore W: $(cat "$WORK/restore.log")"
build A.v >>"$WORK/restore.log" 2>&1 || uc_fail "$NAME restore A: $(cat "$WORK/restore.log")"
cp "$D/W1.v" "$WORK/W.v"
build W.v >"$WORK/rebuild.log" 2>&1 || uc_fail "$NAME rebuild W (AFTER): $(cat "$WORK/rebuild.log")"
build A.v >>"$WORK/rebuild.log" 2>&1 || uc_fail "$NAME rebuild A (AFTER): $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1); c_rc=$?
[ "$c_rc" -eq 0 ] || { echo "$c_out" >&2; uc_fail "$NAME: coqc C.v was refused reusing B.vo -- expected to reuse (control)."; }
uc_same_interface "$WORK" "fa1_functor_argument_reused"
uc_ok "$NAME correctly reused: $(echo "$c_out" | tail -1)"
