#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 23. ACCEPTED OVER-REFUSAL, pinned so a
# later change has to decide it deliberately.
#
# B builds a module type from A's with a `with Definition` constraint.
# Rocq expands the constrained module type inline (declaremods.ml's
# `get_module_sobjs`, MEwith case: "For now, we expand everything, to be
# safe"), so B's own compiled form holds a copy of A.T's fields, and the
# library that copy came from is no longer recoverable from the stored
# objects. The round-23 rule therefore records A as structurally copied
# from the module expression itself, which also refuses this case: A gains
# an unrelated `Module Type U`, which B's copy of A.T cannot observe, so a
# fresh B does compile. Refusing is sound and imprecise; the alternative is
# to trust a case analysis over module-expression shapes, which is what
# rounds 10 to 22 did and what the round-22 hole came out of.
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
mv "$WORK/B.vo" "$WORK/B.stale.vo"
fresh=$(build B.v 2>&1); fresh_rc=$?
[ "$fresh_rc" -eq 0 ] || uc_fail "$NAME fresh B failed, so this is no longer an over-refusal: $fresh"
if [ "$c_rc" -eq 0 ]; then
  uc_fail "$NAME reused a stale B that copies A.T inline -- the round-23 structural rule must refuse it: $c_out"
fi
printf %s "$c_out" | grep -qi inconsistent || uc_fail "$NAME refused for the wrong reason: $c_out"
uc_ok "$NAME refused (sound over-refusal: a fresh B compiles; B copies A.T inline through a with-constraint)"
