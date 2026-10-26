#!/usr/bin/env bash
# Attempted-resolution records (vernac/attempts.ml) and the library label.
#
# Under -location-free-label, library Test.A attempts a resolution that leaves no dependency behind: a
# Require under Fail (binary-equivalence #861's reproduction: the library is
# absent when A is compiled and present later), a Require under Succeed
# (rolled back), a Load under Succeed, a plain Load, a Declare ML Module
# under Fail (no such plugin) and one under Succeed. Each case checks that
# A.vo records the attempt (tools/library_label.exe --attempts), and that
# when what the attempt found changes, A compiled again is another library
# or no longer compiles: its stored digest, the label, changes
# (tools/library_label.exe --stored), and coqc and rocqchk -o refuse Test.B,
# compiled against the first A, over the new one. Compiling A twice in an
# unchanged tree gives the same label, and a library with no such attempt
# stores no record. With STOCK_BIN set to the bin directory of a stock build
# of the same base, that build's rocq and rocqchk do the refusing. Test.B is
# compiled by this rocq in either case: a stock coqc does not know the
# ATTEMPTS object kind, so it cannot load a library that holds one.

set -e

export PATH=$BIN:$PATH
LOAD=${STOCK_BIN:-$BIN}

TOOL=${LIBRARY_LABEL:-}
for t in "$PWD/tools/library_label.exe" "$PWD/../_build/default/test-suite/tools/library_label.exe"; do
  if [ -z "$TOOL" ] && [ -x "$t" ]; then TOOL=$t; fi
done
if [ -z "$TOOL" ]; then
  echo "library_label.exe not found: dune build test-suite/tools/library_label.exe, or set LIBRARY_LABEL"
  exit 1
fi

mkdir -p misc/library-label-attempts
cd misc/library-label-attempts
rm -rf _test
mkdir _test
fail=0

comp() { # comp DIR FILE
  rocq c -q -location-free-label -R "_test/$1" Test "_test/$1/$2.v"
}
label() { "$TOOL" --stored "_test/$1/A.vo"; }
attempts() { "$TOOL" --attempts "_test/$1/A.vo"; }
check() { # check WHAT CONDITION...
  local what=$1; shift
  if "$@"; then echo "PASS $what"; else echo "FAIL $what"; fail=1; fi
}
has() { grep -q -- "$2" <<< "$1"; }
setup() { mkdir -p "_test/$1"; printf '%b' "$2" > "_test/$1/A.v"; }
# dependent DIR: Test.B, compiled against the current Test.A of DIR.
dependent() {
  printf 'Require Test.A.\nDefinition b := 0.\n' > "_test/$1/B.v"
  comp "$1" B
}
# refused DIR: coqc and rocqchk -o refuse Test.B over the current Test.A.
refused() {
  printf 'Require Test.B.\n' > "_test/$1/C.v"
  ! "$LOAD"rocq c -q -R "_test/$1" Test "_test/$1/C.v" > "_test/$1/coqc.log" 2>&1 &&
    grep -q "makes inconsistent assumptions over library Test.A" "_test/$1/coqc.log" &&
    ! "$LOAD"rocqchk -silent -o -R "_test/$1" Test -norec Test.A -norec Test.B > "_test/$1/chk.log" 2>&1 &&
    grep -q "Inconsistent assumptions over module Test.A" "_test/$1/chk.log"
}

# 0. No attempt that nothing else records: no record, a stock file.
setup none "Require Test.Y.\nDefinition a := Test.Y.y.\n"
printf 'Definition y := 0.\n' > _test/none/Y.v
comp none Y; comp none A
check "a plain Require stores no record" test "$(attempts none)" = "no attempts"

# 0b. Without -location-free-label, an attempt is not recorded: a stock file.
setup noflag "Fail Require Test.X.\nDefinition a := 0.\n"
rocq c -q -R _test/noflag Test _test/noflag/A.v
check "without the flag, no record" test "$(attempts noflag)" = "no attempts"

# 1. Require under Fail of a library absent when A is compiled (#861).
setup fail "Fail Require Test.X.\nDefinition a := 0.\n"
comp fail A
r=$(attempts fail); echo "$r"
check "Fail Require: the attempt is recorded" has "$r" "an attempted Require of Test.X"
check "Fail Require: the record says X.vo was absent" has "$r" "fail/X.vo absent"
printf 'Definition x := 0.\n' > _test/fail/X.v
comp fail X
check "Fail Require: once X exists, A no longer compiles" bash -c "! rocq c -q -R _test/fail Test _test/fail/A.v > /dev/null 2>&1"

# 2. Require under Succeed: rolled back, so not a dependency of A.
setup succeed "Succeed Require Test.Y.\nDefinition a := 0.\n"
printf 'Definition y := 0.\n' > _test/succeed/Y.v
comp succeed Y; comp succeed A
r=$(attempts succeed); echo "$r"
check "Succeed Require: the attempt and the file it read are recorded" has "$r" "succeed/Y.vo sha256"
d1=$(label succeed); comp succeed A; d2=$(label succeed)
check "Succeed Require: compiled again, nothing changed: the same label" test "$d1" = "$d2"
dependent succeed
printf 'Definition y := 1.\n' > _test/succeed/Y.v
comp succeed Y; comp succeed A
check "Succeed Require: the library changed: another label" test "$d1" != "$(label succeed)"
check "Succeed Require: coqc and rocqchk refuse the dependent" refused succeed

# 3. Load under Succeed.
setup succeedload "Succeed Load L.\nDefinition a := 0.\n"
printf 'Definition l := 0.\n' > _test/succeedload/L.v
comp succeedload A
r=$(attempts succeedload); echo "$r"
check "Succeed Load: the attempt and the file it read are recorded" has "$r" "succeedload/L.v sha256"
d1=$(label succeedload)
dependent succeedload
printf 'Definition l := 1.\n' > _test/succeedload/L.v
comp succeedload A
check "Succeed Load: the file changed: another label" test "$d1" != "$(label succeedload)"
check "Succeed Load: coqc and rocqchk refuse the dependent" refused succeedload

# 4. A plain Load: it leaves no object either.
setup load "Load L.\nDefinition a := l.\n"
printf 'Definition l := 0.\n' > _test/load/L.v
comp load A
check "Load: the attempt is recorded" has "$(attempts load)" "an attempted Load of L.v"
d1=$(label load)
dependent load
printf 'Definition l := 0.\n(* a comment *)\n' > _test/load/L.v
comp load A
check "Load: the file changed: another label" test "$d1" != "$(label load)"
check "Load: coqc and rocqchk refuse the dependent" refused load

# 5. Declare ML Module under Fail, of a plugin that does not exist.
setup failml "Fail Declare ML Module \"libkey_test_plugin\".\nDefinition a := 0.\n"
comp failml A
r=$(attempts failml); echo "$r"
check "Fail Declare ML Module: the attempt is recorded, nothing read" has "$r" "Declare ML Module of libkey_test_plugin: probes \[\] read \[\]"
d1=$(label failml)
dependent failml
mkdir -p _test/ocamlpath/libkey_test_plugin
printf 'plugin(byte) = "p.cma"\nplugin(native) = "p.cmxs"\n' > _test/ocamlpath/libkey_test_plugin/META
printf 'not a plugin' > _test/ocamlpath/libkey_test_plugin/p.cmxs
cp _test/ocamlpath/libkey_test_plugin/p.cmxs _test/ocamlpath/libkey_test_plugin/p.cma
OCAMLPATH="$PWD/_test/ocamlpath${OCAMLPATH:+:$OCAMLPATH}" comp failml A
check "Fail Declare ML Module: the plugin exists now: another label" test "$d1" != "$(label failml)"
check "Fail Declare ML Module: coqc and rocqchk refuse the dependent" refused failml

# 6. Declare ML Module under Succeed (rolled back): its files change.
setup succeedml "Succeed Declare ML Module \"zarith\".\nDefinition a := 0.\n"
comp succeedml A
check "Succeed Declare ML Module: the plugin's files are recorded" has "$(attempts succeedml)" "zarith.cmxs sha256"
d1=$(label succeedml)
dependent succeedml
zdir=$(ocamlfind query zarith)
mkdir -p _test/zarith-changed
cp -r "$zdir" _test/zarith-changed/zarith
chmod -R u+w _test/zarith-changed
for f in _test/zarith-changed/zarith/*.cmxs _test/zarith-changed/zarith/*.cma; do printf 'x' >> "$f"; done
OCAMLPATH="$PWD/_test/zarith-changed${OCAMLPATH:+:$OCAMLPATH}" comp succeedml A
check "Succeed Declare ML Module: the plugin's files changed: another label" test "$d1" != "$(label succeedml)"
check "Succeed Declare ML Module: coqc and rocqchk refuse the dependent" refused succeedml

exit $fail
