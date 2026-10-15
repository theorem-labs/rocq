#!/usr/bin/env bash
# binary-equivalence-taiga#841, plan-861-commit1 review round 1 finding
# 861C1-R1-3 (load-order toy, `order/o1` vs `order/o2`,
# /mnt/nvme/sami/speed/coord/r1-861c1/order/). KNOWN OPEN GAP, confirmed
# reachable on THIS branch (round 7), not fixed by this round.
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
# D.vo's own kernel-visible content (comp_mod, comp_iface, closure_names/
# closure_none_digest -- the FULL transitive closure is a DirPath.Map,
# unordered) is IDENTICAL between o1 and o2: A and B's own digests don't
# change, and D itself declares nothing beyond requiring them. So
# `digest_match` (`vodigest`, "digest of the seg_lib part" -- the kernel
# LIBRARY SEGMENT only, inherited unchanged from stock) already returns
# TRUE for D between o1 and o2, which means `dep_ok`'s RELAXED fallback
# (this fork's own code) is never even reached -- the stock fast path
# alone accepts the swap. This is a STOCK gap (confirmed independently in
# the plan-861-commit1 review: stock coqc/rocqchk both accept the same
# swap), not something this fork's relaxed-reuse mechanism introduces or
# widens.
#
# Root cause: `vodigest` covers only the kernel library segment, never
# the `vernac/library.ml` SUMMARY's `md_deps` (an array in LOAD order,
# which an unordered `DirPath.Map` erases) or `md_info` (see the sibling
# `info_deprecated_attribute_residual_gap`). Fixing this means widening
# what `vodigest`/`digest_match` cover in the first place, a stock-level
# change bigger than anything this fork's dep_ok fallback can reach by
# itself -- tracked as part of #861 commit 1's own interface (still being
# written; do not build against it yet). Same risk class as the
# documented G8/D1 gap: a dev-loop signal that can lie about what a fresh
# compile would do, never a path to an unsound ACCEPT at grading time
# (grading always recompiles from source).
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
if [ "$g_rc" -ne 0 ]; then
  uc_ok "GAP CLOSED: coqc G.v now refuses to reuse K.vo when D's instance load order changed underneath it ($(echo "$g_out" | grep -im1 'inconsistent assumptions\|error')) -- update this fixture's header, it's no longer a residual gap."
  exit 0
fi

uc_ok "KNOWN RESIDUAL GAP (plan-861-commit1 R1-3, order/): coqc G.v wrongly reused K.vo after D's instance load order changed (a fresh K against the new D fails: $(echo "$fresh_out" | grep -im1 'error')) -- vodigest's library-segment-only scope misses md_deps order; see this file's header for why this fork's dep_ok relaxed fallback is not the cause and cannot close it alone."
