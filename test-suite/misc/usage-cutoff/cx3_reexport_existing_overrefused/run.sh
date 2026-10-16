#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 23. ACCEPTED OVER-REFUSAL (was asserted
# reused). W gains `Require Export Y`, and A already requires Y after W, so
# Y now loads BEFORE W: A's load order changes from [.. W Y] to [.. Y W].
# Load order decides which instance or hint a dependent's proof search
# picks (order_instance_priority_refused), so the round-23 order check
# refuses any dependent whose recorded order is no longer a subsequence of
# the live one. Here neither library declares an instance, so a fresh B
# compiles identically; telling order-sensitive libraries from the rest
# would need a per-object analysis of hints and instances, which the
# check does not attempt.
. ../lib.sh
NAME=$(basename "$(pwd)")
D=$(pwd); WORK="$D/work"; rm -rf "$WORK"; mkdir -p "$WORK"
cp "$D"/*.v "$WORK"/
build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }
cp "$D/W0.v" "$WORK/W.v"
for f in X.v Y.v W.v A.v B.v C.v; do build $f >>"$WORK/setup.log" 2>&1 || uc_fail "$NAME setup $f: $(cat "$WORK/setup.log")"; done
cp "$D/W1.v" "$WORK/W.v"
for f in W.v A.v; do build $f >>"$WORK/rebuild.log" 2>&1 || uc_fail "$NAME rebuild $f: $(cat "$WORK/rebuild.log")"; done
c_out=$(build C.v 2>&1); c_rc=$?
mv "$WORK/B.vo" "$WORK/B.stale.vo"
fresh=$(build B.v 2>&1) || uc_fail "$NAME fresh B failed, so this is no longer an over-refusal: $fresh"
[ "$c_rc" -ne 0 ] || uc_fail "$NAME reused the stale B; the round-23 rule records this case and must refuse it: $c_out"
printf %s "$c_out" | grep -qi inconsistent || uc_fail "$NAME refused for the wrong reason: $c_out"
uc_ok "$NAME refused (sound over-refusal: a fresh B compiles)"
