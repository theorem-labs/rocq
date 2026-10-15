#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 11 (reviewer, issuecomment-
# 6199183929, fixture "mvt"). X has `Module M. Module Type T. Parameter f
# : nat. End T. End M.` (a MODULE TYPE); W adds a top-level `Module T`
# (a MODULE, different kind). B seals `Module Q : T.` -- Rocq's `: T`
# seal syntax only ever resolves a MODULE TYPE, so W's unrelated module T
# is never a candidate: a fresh compile always succeeds. Confirms the
# kind tag (module_label_marker vs modtype_label_marker) keeps the two
# kinds from colliding, so this reuses correctly (not merely refused
# soundly, as nd2/nd3/nd5q/nd5c/nd5b/nd5c are).
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
[ "$fresh_rc" -eq 0 ] || { echo "$fresh_out" >&2; uc_fail "SANITY: fresh B failed -- expected to succeed (: T seal only ever resolves a module type, never W's module T)."; }
rm -f "$WORK"/B_fresh_check.*

cp "$D/W0.v" "$WORK/W.v"
build W.v >"$WORK/restore.log" 2>&1 || uc_fail "restore W: $(cat "$WORK/restore.log")"
build A.v >>"$WORK/restore.log" 2>&1 || uc_fail "restore A: $(cat "$WORK/restore.log")"
cp "$D/W1.v" "$WORK/W.v"
build W.v >"$WORK/rebuild.log" 2>&1 || uc_fail "rebuild W (AFTER): $(cat "$WORK/rebuild.log")"
build A.v >>"$WORK/rebuild.log" 2>&1 || uc_fail "rebuild A (AFTER): $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1); c_rc=$?
[ "$c_rc" -eq 0 ] || { echo "$c_out" >&2; uc_fail "coqc C.v was refused reusing B.vo after an unrelated MODULE T (different kind than X's Module Type T) -- the kind tag must keep these from colliding (mvt)."; }
uc_ok "unrelated same-named Module T (different kind) correctly reused: $(echo "$c_out" | tail -1)"
