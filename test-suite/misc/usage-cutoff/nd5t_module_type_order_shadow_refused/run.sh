#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 11 (reviewer, issuecomment-
# 6199183929, fixture "nd5t"). The nd5 shape for Module Types: X has
# `Module M. Module Type T. Parameter f : nat. End T. End M.`; W adds a
# top-level `Module Type T. Parameter zzq : nat. End T.`; B does `Import
# M. Require Import A.` then seals `Module Q : T. Definition f := 1. End
# Q.` A TRUE shadow: a fresh compile fails (missing field zzq).
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
[ "$fresh_rc" -ne 0 ] || { echo "$fresh_out" >&2; uc_fail "SANITY: fresh B succeeded -- this fixture does not exercise a real shadow."; }
echo "$fresh_out" | grep -q "is missing in" || uc_fail "fresh B did not fail with the expected missing-field error: $fresh_out"
rm -f "$WORK"/B_fresh_check.*

cp "$D/W0.v" "$WORK/W.v"
build W.v >"$WORK/restore.log" 2>&1 || uc_fail "restore W: $(cat "$WORK/restore.log")"
build A.v >>"$WORK/restore.log" 2>&1 || uc_fail "restore A: $(cat "$WORK/restore.log")"
cp "$D/W1.v" "$WORK/W.v"
build W.v >"$WORK/rebuild.log" 2>&1 || uc_fail "rebuild W (AFTER): $(cat "$WORK/rebuild.log")"
build A.v >>"$WORK/rebuild.log" 2>&1 || uc_fail "rebuild A (AFTER): $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1); c_rc=$?
[ "$c_rc" -ne 0 ] || { echo "$c_out" >&2; uc_fail "coqc C.v reused B.vo after a TRUE Module-Type shadow -- must refuse (nd5t)."; }
echo "$c_out" | grep -qi 'inconsistent assumptions' || uc_fail "wrong refusal message: $c_out"
uc_ok "order-dependent Module Type T shadow correctly refused: $(echo "$c_out" | grep -im1 'inconsistent assumptions')"
