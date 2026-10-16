#!/usr/bin/env bash
# binary-equivalence-taiga#841 Review841 round 9 (Lean round 9 review,
# issuecomment-6193279748, fixture "mkc2"). CONTROL for mkc1: the SAME
# shape, but W's new unrelated Module Type U names its field "u", not "x"
# -- no marked-basename collision with X's Module Type T at all
# ("0usage_cutoff_modtype_u" vs "0usage_cutoff_modtype_x"). Already
# correctly REUSED before and after the P3 fix; isolates mkc1's bug to the
# collision specifically, not to module types sharing a library in
# general.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/A.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/W0.v" "$WORK/W.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build W.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build W.v (BEFORE): $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (unchanged across both phases): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, uses only g): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"

cp "$D/W1.v" "$WORK/W.v"
build W.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD W (AFTER, adds unrelated Module Type U with a non-colliding field) failed unexpectedly: $(cat "$WORK/rebuild.log")"
build A.v >>"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (same source, against W1.v) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -ne 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v was refused reusing B.vo after W added an unrelated, non-field-colliding Module Type U -- this control is expected to always reuse, with or without the P3 fix."
fi
uc_same_interface "$WORK" "mkc2_module_type_distinct_field_reused"
uc_ok "unrelated, non-colliding Module Type U correctly reused: $(echo "$c_out" | tail -1)"
