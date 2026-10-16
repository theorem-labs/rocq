#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 23. ACCEPTED OVER-REFUSAL, pinned.
#
# B applies X's functor to A's module M. The application does not copy A.M's
# own field list into B: R's fields come from the functor's parameter
# signature S, so an addition to A (here an unrelated top-level definition)
# cannot change a fresh B. A change INSIDE A.M, or to S, is already refused
# by the per-declaration interface digest.
#
# The round-23 rule records a functor argument's library as structurally
# copied anyway, because the argument's path appears only inside the
# application's substitution and separating "copied" from "merely named"
# means a case analysis over module-expression shapes -- which is how the
# round-22 hole arose. The cost is this refusal; the fixture exists so a
# later change to that rule has to face it deliberately.
. ../lib.sh
NAME=$(basename "$(pwd)")
D=$(pwd); WORK="$D/work"; rm -rf "$WORK"; mkdir -p "$WORK"
cp "$D"/X.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A0.v" "$WORK/A.v"
build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }
for f in X.v A.v B.v C.v; do
  build $f >>"$WORK/setup.log" 2>&1 || uc_fail "$NAME setup $f: $(cat "$WORK/setup.log")"
done
cp "$D/A1.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "$NAME rebuild A: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1); c_rc=$?
mv "$WORK/B.vo" "$WORK/B.stale.vo"
fresh=$(build B.v 2>&1); fresh_rc=$?
[ "$fresh_rc" -eq 0 ] || uc_fail "$NAME fresh B failed, so this is no longer an over-refusal: $fresh"
[ "$c_rc" -eq 0 ] && uc_fail "$NAME reused a stale B that applies a functor to a module of the changed library; the round-23 rule must refuse it: $c_out"
printf %s "$c_out" | grep -qi inconsistent || uc_fail "$NAME refused for the wrong reason: $c_out"
uc_ok "$NAME refused (sound over-refusal: a fresh B compiles)"
