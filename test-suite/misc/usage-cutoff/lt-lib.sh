#!/usr/bin/env bash
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"

uc_direct_vernac() {
  local expected=$1
  local name=$(basename "$PWD")
  local dir=$PWD
  local work="$dir/work"
  mkdir -p "$work"
  cp "$dir"/X.v "$dir"/B.v "$dir"/C.v "$work"/
  test ! -f "$dir/Y.v" || cp "$dir/Y.v" "$work/Y.v"
  cp "$dir/A0.v" "$work/A.v"
  build() { ( cd "$work" && uc_coqc -Q . "" "$1" ); }
  test ! -f "$work/Y.v" || build Y.v >"$work/setup.log" 2>&1 || uc_fail "$name setup Y"
  build X.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup X"
  build A.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup A0"
  build B.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup B"
  build C.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup C"
  cp "$dir/A1.v" "$work/A.v"
  build A.v >"$work/after.log" 2>&1 || uc_fail "$name rebuild A1"
  cp "$dir/B.v" "$work/B_fresh_check.v"
  fresh_out=$(cd "$work" && uc_coqc -Q . "" B_fresh_check.v 2>&1); fresh_rc=$?
  c_out=$(build C.v 2>&1); c_rc=$?
  if [ "$expected" = refused ]; then
    [ "$fresh_rc" -ne 0 ] || uc_fail "$name fresh B unexpectedly succeeded"
    [ "$c_rc" -ne 0 ] || uc_fail "$name reused stale B where fresh B fails"
    printf %s "$c_out" | grep -qi inconsistent || uc_fail "$name refused for the wrong reason: $c_out"
    uc_ok "$name correctly refused"
  elif [ "$expected" = overrefused ]; then
    [ "$fresh_rc" -eq 0 ] || uc_fail "$name fresh B unexpectedly failed: $fresh_out"
    [ "$c_rc" -ne 0 ] || uc_fail "$name reused despite expected P3 refusal"
    printf %s "$c_out" | grep -qi inconsistent || uc_fail "$name refused for the wrong reason: $c_out"
    uc_ok "$name correctly over-refused"
  else
    [ "$fresh_rc" -eq 0 ] || uc_fail "$name fresh B unexpectedly failed: $fresh_out"
    [ "$c_rc" -eq 0 ] || uc_fail "$name refused a valid reuse: $c_out"
    uc_same_interface "$work" "$name"
    uc_ok "$name correctly reused"
  fi
}
