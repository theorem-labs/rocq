#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "dropped_transitive_dep_clean_refusal"
# (added for Review841's G8/e6). A drops a plain, non-Export `Require X.`
# that B's own `b := X.f` transitively depends on; the stale B.vo's reuse
# must be refused CLEANLY (a catchable user error), never crash with a raw
# kernel Anomaly or silently accept a dangling reference.
#
# Case (a): C.v forces `b` to actually be reduced (`Eval compute in b.` --
# `Check`/`Print` do NOT force it, since neither needs the kernel to
# dereference the stored Constr's reference to X.f).
# Case (b): C_unused.v requires B but never forces `b` at all.
#
# Round 10/11 review (binary-equivalence-taiga#841 round 10 comment): this
# test's PREVIOUS version gated on a literal `comp_transitive_deps :` field
# definition (commit 1/D1's own tuple-widening, not yet landed) and
# asserted the OLD buggy pre-D1 behavior (an Anomaly for case (a), a silent
# accept for case (b)) as its "current" branch. That gate is dropped here:
# the review ran both cases directly against this branch and found BOTH
# already produce a clean refusal -- B's recorded closure table (G7's
# `closure_table`/`closure_subset_ok`, landed since round 5, no relation to
# D1's own `comp_transitive_deps` field) already contains `X.f`, which is
# missing from the live closure once A drops its Require of X, so
# `dep_ok`'s existing closure check refuses the reuse before either case
# ever reaches a raw kernel lookup or digest_of_dep's own Anomaly-prone
# path. This is NOT evidence D1/commit-1 landed (it hasn't): it is G7's
# OWN, already-shipped mechanism correctly closing e6 by a different route
# than the one this test originally expected to need.
. ../lib.sh

# The scenario above must be a clean refusal in BOTH sub-cases -- no
# Anomaly, no silent accept.
D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/B.v "$D"/C.v "$D"/C_unused.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE, requires X): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, uses X.f): $(cat "$WORK/setup.log")"

cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, drops Require of X) failed unexpectedly: $(cat "$WORK/rebuild.log")"

a_out=$(build C.v 2>&1)
a_rc=$?
if [ "$a_rc" -eq 0 ]; then
  echo "$a_out" >&2
  uc_fail "coqc C.v succeeded forcing b (Eval compute) after A dropped its transitive dependency on X -- the dropped dependency was not detected at all."
fi
echo "$a_out" | grep -qi 'anomaly' \
  && uc_fail "coqc C.v refused case (a), but with a raw Anomaly rather than a clean user-facing error -- G8's fix did not take effect. Got: $a_out"
echo "$a_out" | grep -qi -E 'inconsistent assumptions|unknown module|reference to unknown' \
  || uc_fail "coqc C.v refused case (a) (exit $a_rc) but not with a recognizable clean refusal message -- got: $a_out"

b_out=$(build C_unused.v 2>&1)
b_rc=$?
if [ "$b_rc" -eq 0 ]; then
  echo "$b_out" >&2
  uc_fail "coqc C_unused.v succeeded requiring B (without ever using b) after A dropped its transitive dependency on X -- case (b)'s silent accept is still present even though D1 landed."
fi
echo "$b_out" | grep -qi -E 'inconsistent assumptions|unknown module|reference to unknown' \
  || uc_fail "coqc C_unused.v refused case (b) (exit $b_rc) but not with a recognizable clean refusal message -- got: $b_out"

uc_ok "both e6 sub-cases produce a clean refusal via G7's existing closure check -- case (a): $(echo "$a_out" | grep -im1 -E 'inconsistent assumptions|unknown module|reference to unknown'); case (b): $(echo "$b_out" | grep -im1 -E 'inconsistent assumptions|unknown module|reference to unknown')"
