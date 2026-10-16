#!/usr/bin/env bash
# Exact round-16 fixture protocol from binary-equivalence-taiga#841
# issuecomment-6201592452. The first argument is refused or reused.
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"

uc_round16() {
  local expected=$1
  local name
  local dir=$PWD
  local work="$dir/work"
  name=$(basename "$dir")
  mkdir -p "$work"
  cp "$dir"/X.v "$dir"/A.v "$dir"/B.v "$dir"/C.v "$work"/
  test ! -f "$dir/Y.v" || cp "$dir/Y.v" "$work/Y.v"
  test ! -f "$dir/Y2.v" || cp "$dir/Y2.v" "$work/Y2.v"
  cp "$dir/W0.v" "$work/W.v"
  build() { ( cd "$work" && uc_coqc -Q . "" "$1" ); }
  build X.v >"$work/setup.log" 2>&1 || uc_fail "$name setup X: $(cat "$work/setup.log")"
  test ! -f "$work/Y.v" || build Y.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup Y: $(cat "$work/setup.log")"
  test ! -f "$work/Y2.v" || build Y2.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup Y2: $(cat "$work/setup.log")"
  build W.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup W0: $(cat "$work/setup.log")"
  build A.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup A: $(cat "$work/setup.log")"
  build B.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup B: $(cat "$work/setup.log")"
  build C.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup C: $(cat "$work/setup.log")"

  cp "$dir/W1.v" "$work/W.v"
  build W.v >"$work/after.log" 2>&1 || uc_fail "$name rebuild W1: $(cat "$work/after.log")"
  build A.v >>"$work/after.log" 2>&1 || uc_fail "$name rebuild A: $(cat "$work/after.log")"
  cp "$dir/B.v" "$work/B_fresh_check.v"
  fresh_out=$(cd "$work" && uc_coqc -Q . "" B_fresh_check.v 2>&1); fresh_rc=$?
  if [ "$expected" = refused ]; then
    [ "$fresh_rc" -ne 0 ] || uc_fail "$name sanity: fresh B unexpectedly succeeded"
  else
    [ "$fresh_rc" -eq 0 ] || uc_fail "$name sanity: fresh B unexpectedly failed: $fresh_out"
  fi

  cp "$dir/W0.v" "$work/W.v"
  build W.v >"$work/restore.log" 2>&1 || uc_fail "$name restore W0: $(cat "$work/restore.log")"
  build A.v >>"$work/restore.log" 2>&1 || uc_fail "$name restore A: $(cat "$work/restore.log")"
  cp "$dir/W1.v" "$work/W.v"
  build W.v >"$work/rebuild.log" 2>&1 || uc_fail "$name restore W1: $(cat "$work/rebuild.log")"
  build A.v >>"$work/rebuild.log" 2>&1 || uc_fail "$name restore A1: $(cat "$work/rebuild.log")"
  c_out=$(build C.v 2>&1); c_rc=$?
  if [ "$expected" = refused ]; then
    [ "$c_rc" -ne 0 ] || uc_fail "$name reused stale B where fresh B fails"
    printf %s "$c_out" | grep -qi inconsistent || uc_fail "$name refused for the wrong reason: $c_out"
    uc_ok "$name correctly refused"
  elif [ "$expected" = overrefused ]; then
    [ "$c_rc" -ne 0 ] || uc_fail "$name reused despite the expected P3 refusal"
    printf %s "$c_out" | grep -qi inconsistent || uc_fail "$name refused for the wrong reason: $c_out"
    uc_ok "$name correctly over-refused"
  else
    [ "$c_rc" -eq 0 ] || uc_fail "$name refused a valid reuse: $c_out"
    uc_same_interface "$work" "$name"
    uc_ok "$name correctly reused"
  fi
}
