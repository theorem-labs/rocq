#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 23, speed-coord review plan-861c1-r1
# finding R1-1. A primitive string literal carries arbitrary bytes an agent
# chooses, so it is the one place where a hash collision is constructible
# rather than hypothetical. This fixture pins the ordinary case: changing
# the literal in a dependency must refuse every dependent that uses it.
#
# The collision argument itself is about which hash the decision rests on,
# not about this verdict: every digest the reuse decision computes over
# agent-controlled bytes is SHA-256 (clib/csha256.ml), and the one MD5
# value in the chain is stock Rocq's own whole-library digest, which the
# round-23 structural check requires IN ADDITION to a SHA-256 interface
# identity (kernel/safe_typing.ml, `structural_dep`).
. ../lib.sh
NAME=$(basename "$(pwd)")
D=$(pwd); WORK="$D/work"; rm -rf "$WORK"; mkdir -p "$WORK"
cp "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A0.v" "$WORK/A.v"
build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }
build A.v >"$WORK/setup.log" 2>&1 || uc_fail "$NAME setup A: $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "$NAME setup B: $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "$NAME setup C: $(cat "$WORK/setup.log")"
cp "$D/A1.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "$NAME rebuild A: $(cat "$WORK/rebuild.log")"
c_out=$(build C.v 2>&1); c_rc=$?
[ "$c_rc" -ne 0 ] || uc_fail "$NAME reused a stale B after the primitive string literal it depends on changed: $c_out"
printf %s "$c_out" | grep -qi inconsistent || uc_fail "$NAME refused for the wrong reason: $c_out"
uc_ok "$NAME correctly refused after a %pstring literal change"
