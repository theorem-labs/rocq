#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 23. ACCEPTED OVER-REFUSAL (was asserted
# reused from round 22, 4be0c270eb). B seals M with A's module type T, and A
# gains an unrelated Module Type U, so a fresh B compiles identically. The
# round-23 structural rule records every module path a module expression in
# B names, the sealing signature T included, so B now depends on A's whole
# interface and refuses. Telling a signature position from a copying one is
# exactly the per-shape reasoning rounds 10-22 accumulated and the round-22
# hole came out of; the rule is conservative by construction instead.
. ../lib.sh
NAME=$(basename "$(pwd)")
D=$(pwd); WORK="$D/work"; rm -rf "$WORK"; mkdir -p "$WORK"
cp "$D"/*.v "$WORK"/
build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }
cp "$D/A0.v" "$WORK/A.v"
for f in X.v A.v B.v C.v; do build $f >>"$WORK/setup.log" 2>&1 || uc_fail "$NAME setup $f: $(cat "$WORK/setup.log")"; done
cp "$D/A1.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "$NAME rebuild A: $(cat "$WORK/rebuild.log")"
c_out=$(build C.v 2>&1); c_rc=$?
mv "$WORK/B.vo" "$WORK/B.stale.vo"
fresh=$(build B.v 2>&1) || uc_fail "$NAME fresh B failed, so this is no longer an over-refusal: $fresh"
[ "$c_rc" -ne 0 ] || uc_fail "$NAME reused the stale B; the round-23 rule records this case and must refuse it: $c_out"
printf %s "$c_out" | grep -qi inconsistent || uc_fail "$NAME refused for the wrong reason: $c_out"
uc_ok "$NAME refused (sound over-refusal: a fresh B compiles)"
