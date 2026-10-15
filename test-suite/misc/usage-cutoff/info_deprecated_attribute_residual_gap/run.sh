#!/usr/bin/env bash
# binary-equivalence-taiga#841, plan-861-commit1 review round 1 finding
# 861C1-R1-3 (library-info toy, `info/i1` vs `info/i2`,
# /mnt/nvme/sami/speed/coord/r1-861c1/info/). KNOWN OPEN GAP, confirmed
# reachable on THIS branch (round 7), not fixed by this round. Same root
# cause as the sibling `order_instance_priority_residual_gap` -- see that
# fixture's header for the full argument (vodigest covers only the kernel
# library segment, never `vernac/library.ml`'s summary `md_info`; this
# fork's dep_ok relaxed fallback is never even reached, since the stock
# fast path `digest_match` already accepts the swap).
#
# `D_i1.v`/`D_i2.v` both declare the SAME `Definition d := 0.`; i2 adds
# `Attributes deprecated(note="x").` on it, a LIBRARY-FILE-level
# attribute with no kernel-visible effect on `d`'s own declaration (its
# SFBconst digest is identical either way). A dependent compiled with
# `Set Warnings "+deprecated"` genuinely differs: it succeeds requiring
# i1's D, and ERRORS requiring i2's D ("Library File ... is deprecated"
# promoted to an error by the `+deprecated` warning setting).
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/K.v "$D"/G.v "$WORK"/

build() { ( cd "$WORK" && uc_coqc -Q . T "$1" ); }

cp "$D/D_i1.v" "$WORK/D.v"
build D.v >"$WORK/i1.log" 2>&1 || uc_fail "SETUP: could not build D.v (i1): $(cat "$WORK/i1.log")"
build K.v >>"$WORK/i1.log" 2>&1 || uc_fail "SETUP: could not build K.v against i1's D: $(cat "$WORK/i1.log")"
cp "$WORK/D.vo" "$WORK/D.vo.i1"
cp "$WORK/K.vo" "$WORK/K.vo.i1built"

# Sanity: a FRESH K against i2's D really does differ (errors, since
# +deprecated promotes the library-deprecation warning to an error).
rm -f "$WORK"/D.vo "$WORK"/D.glob
cp "$D/D_i2.v" "$WORK/D.v"
build D.v >"$WORK/i2.log" 2>&1 || uc_fail "SETUP: could not build D.v (i2, Attributes deprecated): $(cat "$WORK/i2.log")"
cp "$WORK/D.vo" "$WORK/D.vo.i2"
rm -f "$WORK"/K.vo "$WORK"/K.glob
fresh_out=$(build K.v 2>&1)
fresh_rc=$?
if [ "$fresh_rc" -eq 0 ]; then
  echo "$fresh_out" >&2
  uc_fail "SANITY: a fresh compile of K against i2's deprecated D succeeded -- this fixture does not actually exercise the deprecation hazard, nothing to test."
fi
d_before_hash=$(uc_sha256 "$WORK/D.vo.i1")
d_after_hash=$(uc_sha256 "$WORK/D.vo.i2")
if [ "$d_before_hash" = "$d_after_hash" ]; then
  uc_fail "SANITY: D.vo is byte-identical between i1 and i2 -- the deprecation-attribute toy does not actually produce a different .vo, nothing to test."
fi

# Restore K.vo (built against i1's D) and swap D.vo to i2's -- exactly
# like the fork's own relaxed check_required would see at any later
# `Require T.K.`.
cp "$WORK/K.vo.i1built" "$WORK/K.vo"
cp "$WORK/D.vo.i2" "$WORK/D.vo"

g_out=$(build G.v 2>&1)
g_rc=$?
if [ "$g_rc" -ne 0 ]; then
  uc_ok "GAP CLOSED: coqc G.v now refuses to reuse K.vo when D gained a deprecation attribute underneath it ($(echo "$g_out" | grep -im1 'inconsistent assumptions\|error\|deprecated')) -- update this fixture's header, it's no longer a residual gap."
  exit 0
fi

uc_ok "KNOWN RESIDUAL GAP (plan-861-commit1 R1-3, info/): coqc G.v wrongly reused K.vo after D gained a deprecation attribute (a fresh K against the new D errors: $(echo "$fresh_out" | grep -im1 'deprecated')) -- vodigest's library-segment-only scope misses md_info; see this file's header for why this fork's dep_ok relaxed fallback is not the cause and cannot close it alone."
