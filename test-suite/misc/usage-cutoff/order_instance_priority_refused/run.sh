#!/usr/bin/env bash
# binary-equivalence-taiga#841, speed-coord review plan-861c1-r1 finding
# R1-3 (load-order toy, `order/o1` vs `order/o2`). Was a documented open
# gap through round 22; closed in round 23 and asserted here.
#
# `Cl.v` declares a typeclass `C`; `A.v`/`B.v` each declare a `#[global]
# Instance` of `C` (compiled to an ordinary SFBconst each, so their OWN
# digests are identical regardless of anything in D). `D.v` requires both
# -- `D_o1.v` requires A then B, `D_o2.v` requires B then A -- and declares
# nothing else. `K.v` resolves `@v _` via typeclass search, which picks
# the MOST RECENTLY LOADED matching instance: `b` (v=1) under o1's order,
# `a` (v=0) under o2's. A fresh compile of K genuinely differs (confirmed
# below): it succeeds against o1, fails against o2.
#
# What used to let the stale K through: D's load order lives in the
# summary segment's `md_deps`, and every digest a dependent compares is
# computed from the kernel library segment, where requirements are a
# sorted map. Both `digest_match` and the relaxed fallback therefore saw
# o1's D and o2's D as the same library. Round 23 folds the load order
# (and the file-level attributes, see `info_deprecated_attribute_refused`)
# into the exact-compared objects digest at `Declaremods.end_library`, so
# D's own segment bytes differ and every dependent of D refuses.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/Cl.v "$D"/A.v "$D"/B.v "$D"/K.v "$D"/G.v "$WORK"/

build() { ( cd "$WORK" && uc_coqc -Q . T "$1" ); }

build Cl.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build Cl.v: $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v: $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v: $(cat "$WORK/setup.log")"

cp "$D/D_o1.v" "$WORK/D.v"
build D.v >"$WORK/o1.log" 2>&1 || uc_fail "SETUP: could not build D.v (o1, Require A then B): $(cat "$WORK/o1.log")"
build K.v >>"$WORK/o1.log" 2>&1 || uc_fail "SETUP: could not build K.v against o1's D: $(cat "$WORK/o1.log")"
cp "$WORK/D.vo" "$WORK/D.vo.o1"
cp "$WORK/K.vo" "$WORK/K.vo.o1built"

# Sanity: a FRESH K against o2's D really does differ (fails).
rm -f "$WORK"/D.vo "$WORK"/D.glob
cp "$D/D_o2.v" "$WORK/D.v"
build D.v >"$WORK/o2.log" 2>&1 || uc_fail "SETUP: could not build D.v (o2, Require B then A): $(cat "$WORK/o2.log")"
cp "$WORK/D.vo" "$WORK/D.vo.o2"
rm -f "$WORK"/K.vo "$WORK"/K.glob
fresh_out=$(build K.v 2>&1)
fresh_rc=$?
if [ "$fresh_rc" -eq 0 ]; then
  echo "$fresh_out" >&2
  uc_fail "SANITY: a fresh compile of K against o2's D succeeded -- this fixture does not actually exercise an instance-priority hazard, nothing to test."
fi
d_before_hash=$(uc_sha256 "$WORK/D.vo.o1")
d_after_hash=$(uc_sha256 "$WORK/D.vo.o2")
if [ "$d_before_hash" = "$d_after_hash" ]; then
  uc_fail "SANITY: D.vo is byte-identical between o1 and o2 -- the require-order toy does not actually produce a different .vo, nothing to test."
fi

# Restore K.vo (built against o1's D) and swap D.vo to o2's -- exactly
# like the fork's own relaxed check_required would see at any later
# `Require T.K.`.
cp "$WORK/K.vo.o1built" "$WORK/K.vo"
cp "$WORK/D.vo.o2" "$WORK/D.vo"

g_out=$(build G.v 2>&1)
g_rc=$?
if [ "$g_rc" -eq 0 ]; then
  uc_fail "coqc G.v reused K.vo after D's instance load order changed underneath it, although a fresh K against the new D fails: $(echo "$fresh_out" | grep -im1 'error')"
fi
printf %s "$g_out" | grep -qi 'inconsistent assumptions' \
  || uc_fail "G.v was refused for the wrong reason: $g_out"
uc_ok "require-order change in D correctly refused the stale K.vo"
