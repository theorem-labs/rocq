#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 11 (reviewer, issuecomment-
# 6199183929, fixture "mvt2"). Symmetric to mvt: X has `Module M. Module
# N. Definition f := 1. End N. End M.` (a MODULE); W adds a top-level
# `Module Type N` (a MODULE TYPE, different kind). B does `Import N.` --
# `Import` only ever resolves a MODULE, so W's unrelated module type N is
# never a candidate: a fresh compile always succeeds, and reuse must stay
# correct too.
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
[ "$fresh_rc" -eq 0 ] || { echo "$fresh_out" >&2; uc_fail "SANITY: fresh B failed -- expected to succeed (Import only ever resolves a module, never W's module type N)."; }
rm -f "$WORK"/B_fresh_check.*

cp "$D/W0.v" "$WORK/W.v"
build W.v >"$WORK/restore.log" 2>&1 || uc_fail "restore W: $(cat "$WORK/restore.log")"
build A.v >>"$WORK/restore.log" 2>&1 || uc_fail "restore A: $(cat "$WORK/restore.log")"
cp "$D/W1.v" "$WORK/W.v"
build W.v >"$WORK/rebuild.log" 2>&1 || uc_fail "rebuild W (AFTER): $(cat "$WORK/rebuild.log")"
build A.v >>"$WORK/rebuild.log" 2>&1 || uc_fail "rebuild A (AFTER): $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1); c_rc=$?
[ "$c_rc" -eq 0 ] || { echo "$c_out" >&2; uc_fail "coqc C.v was refused reusing B.vo after an unrelated Module Type N (different kind than X's module N) -- the kind tag must keep these from colliding (mvt2)."; }
uc_same_interface "$WORK" "mvt2_module_vs_module_type_reused"
uc_ok "unrelated same-named Module Type N (different kind) correctly reused: $(echo "$c_out" | tail -1)"
