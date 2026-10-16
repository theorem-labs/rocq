#!/usr/bin/env bash
# sl4 (#841 round 21 review, issuecomment-6206055352): A's T gains w, and the
# module X that B seals against T already defines w, so a fresh B compiles.
# The output interface still changes: X.w becomes visible. Against a stale
# B.vo, `Check B.X.w` raised an Anomaly; against a fresh B it prints
# `B.X.w : nat`. So this checks C1's OUTPUT, not just whether fresh B builds:
# stale reuse must be refused, and fresh C1 must see B.X.w.
. ../lib.sh
name=$(basename "$PWD"); dir=$PWD; work="$dir/work"; rm -rf "$work"; mkdir -p "$work"
cp "$dir"/X.v "$dir"/B.v "$dir"/C.v "$dir"/C1.v "$work"/; cp "$dir/A0.v" "$work/A.v"
build() { ( cd "$work" && uc_coqc -Q . "" "$1" ); }
for f in X A B C; do build $f.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup $f: $(cat "$work/setup.log")"; done
cp "$dir/A1.v" "$work/A.v"; build A.v >"$work/after.log" 2>&1 || uc_fail "$name rebuild A1"
stale_out=$(build C1.v 2>&1); stale_rc=$?
cp "$work/B.vo" "$work/B.kept"; build B.v >"$work/freshB.log" 2>&1 || uc_fail "$name fresh B failed: $(cat "$work/freshB.log")"
fresh_out=$(build C1.v 2>&1) || uc_fail "$name fresh C1 failed: $fresh_out"
printf %s "$fresh_out" | grep -q "X.w" || uc_fail "$name fresh C1 does not show X.w: $fresh_out"
[ "$stale_rc" -ne 0 ] || [ "$stale_out" = "$fresh_out" ] || uc_fail "$name stale B reused with different C1 output: $stale_out"
[ "$stale_rc" -ne 0 ] || uc_fail "$name reused stale B whose sealed output interface changed"
printf %s "$stale_out" | grep -qi inconsistent || uc_fail "$name refused for the wrong reason: $stale_out"
uc_ok "$name correctly refused; fresh C1 sees B.X.w"
