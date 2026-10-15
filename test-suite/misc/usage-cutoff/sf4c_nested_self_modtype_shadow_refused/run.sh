#!/usr/bin/env bash
# Exact sf4c fixture from #841 issuecomment-6201592452.
. "../lib.sh"
name=$(basename "$PWD")
dir=$PWD
work="$dir/work"
mkdir -p "$work"
cp "$dir"/X.v "$dir"/A.v "$dir"/B.v "$dir"/C.v "$work"/
cp "$dir/W0.v" "$work/W.v"
build() { ( cd "$work" && uc_coqc -Q . "" "$1" ); }
build X.v >"$work/setup.log" 2>&1 || uc_fail "$name setup X"
build W.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup W0"
build A.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup A0"
build B.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup B0"
build C.v >>"$work/setup.log" 2>&1 || uc_fail "$name setup C0"
cp "$dir/W1.v" "$work/W.v"
build W.v >"$work/after.log" 2>&1 || uc_fail "$name rebuild W1"
build A.v >>"$work/after.log" 2>&1 || uc_fail "$name rebuild A1"
build B.v >>"$work/after.log" 2>&1 || uc_fail "$name fresh B unexpectedly failed"
fresh_c_out=$(build C.v 2>&1); fresh_c_rc=$?
[ "$fresh_c_rc" -ne 0 ] || uc_fail "$name sanity: C unexpectedly compiled against fresh B"
cp "$dir/W0.v" "$work/W.v"
build W.v >"$work/restore.log" 2>&1 || uc_fail "$name restore W0"
build A.v >>"$work/restore.log" 2>&1 || uc_fail "$name restore A0"
build B.v >>"$work/restore.log" 2>&1 || uc_fail "$name restore B0"
cp "$dir/W1.v" "$work/W.v"
build W.v >"$work/rebuild.log" 2>&1 || uc_fail "$name rebuild W1"
build A.v >>"$work/rebuild.log" 2>&1 || uc_fail "$name rebuild A1"
c_out=$(build C.v 2>&1); c_rc=$?
[ "$c_rc" -ne 0 ] || uc_fail "$name reused stale B where fresh B changes C"
printf %s "$c_out" | grep -qi inconsistent || uc_fail "$name refused for the wrong reason: $c_out"
uc_ok "$name correctly refused"
