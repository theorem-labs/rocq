#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 9 (Lean round 9 review,
# issuecomment-6193279748, fixture "mtns2"). CONTROL for mtns1: the SAME
# shape of addition, `Module Type T2. Parameter zzq : nat. End T2.`, added
# DIRECTLY to A's own source (not reached transitively through a
# dependency's `Require Export`). T2 shadows nothing B names, so a fresh B
# succeeds and reuse is expected; the stale B must export the same interface
# as a fresh B. An empty filtered Module Type wrapper no longer enters A's
# exact objects digest (mtunrel0, #841 round 21 review); before that, this
# case was refused there. mtns3 is the direct addition that shadows X.T.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, T resolves to X.T): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, direct Module Type T2 addition) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1) || uc_fail "coqc C.v refused a valid reuse after A directly added the unrelated Module Type T2: $c_out"
uc_same_interface "$WORK" mtns2
fresh_c=$(build C.v 2>&1) || uc_fail "coqc C.v failed against a fresh B: $fresh_c"
[ "$c_out" = "$fresh_c" ] || uc_fail "C output differs between stale and fresh B: stale=[$c_out] fresh=[$fresh_c]"

uc_ok "direct unrelated Module Type T2 addition in A correctly reused; C output and B interface match a fresh build"
