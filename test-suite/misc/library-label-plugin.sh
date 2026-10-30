#!/usr/bin/env bash
# Plugin files and the library label (label version 4, BET-342).
#
# Up to label version 3 the key held the digest of each plugin file a
# library declares, through the ML-MODULE object (vernac/mltop.ml) and
# through the SHA-256 of the files an attempted Declare ML Module resolved
# to (vernac/attempts.ml); version 4 holds the plugin names and the files
# findlib resolved them to, not their content (vernac/libkeyObjects.mli).
#
# Here one findlib package is built twice, at one path, from two
# implementations (its .cmxs bytes differ, what it registers does not), and
# library Test.A is compiled at one path against each build:
# - a plain Declare ML Module: the two A.vo files differ (the object still
#   stores the digests) and their labels are equal, so Test.B, compiled
#   against the first, loads over the second under coqc and rocqchk -o;
# - a Declare ML Module under Succeed (rolled back, so only the ATTEMPTS
#   record holds it): the same, and the record still carries the SHA-256;
# - a second package of the same content under another name: another label,
#   because the names are in the key.
# rocq-library-label --layout-version prints the layout version these labels
# are made by.
#
# Unlike misc/library-label.sh, this test never runs a stock build: both of
# its libraries hold an object kind (ML-MODULE with no digests in its key,
# or ATTEMPTS) that a stock coqc reads differently or not at all.

set -e

export PATH=$BIN:$PATH

. misc/library-label-tool.inc

mkdir -p misc/library-label-plugin
cd misc/library-label-plugin
rm -rf _test
mkdir _test
fail=0

differ() { ! cmp -s "$1" "$2"; }

# plugin NAME BODY: the findlib package NAME, built from BODY, at one path.
# Only the implementation differs between two calls with the same NAME: the
# package registers nothing either way, as a rebuilt plugin of an unchanged
# source registers what it always did.
plugin() {
  mkdir -p "_test/pkg/$1"
  printf 'plugin(byte) = "p.cma"\nplugin(native) = "p.cmxs"\n' > "_test/pkg/$1/META"
  printf '%s\n' "$2" > "_test/pkg/$1/p.ml"
  ( cd "_test/pkg/$1" &&
    ocamlfind ocamlopt -shared -o p.cmxs p.ml > build.log 2>&1 &&
    ocamlfind ocamlc -a -o p.cma p.ml >> build.log 2>&1 ) ||
    { echo "FAIL cannot build the test plugin $1"; cat "_test/pkg/$1/build.log"; exit 1; }
}

export OCAMLPATH="$PWD/_test/pkg${OCAMLPATH:+:$OCAMLPATH}"

# comp DIR: Test.A of DIR, compiled at its own path.
comp() { rocq c -q -location-free-label -R "_test/$1" Test "_test/$1/A.v"; }
# label DIR [FILE]: the digest DIR's FILE stores (A.vo by default).
label() { "$TOOL" --stored "_test/$1/${2:-A.vo}"; }
# same_label DIR: DIR's A.vo and the copy kept before the plugin rebuild
# store one digest, and it is a digest (an empty reading is not a match).
same_label() {
  local a; a=$(label "$1" first.vo)
  [ -n "$a" ] && [ "$a" = "$(label "$1")" ]
}

# case_ DIR DECLARATION: Test.A is compiled against the first build of the
# plugin and kept as first.vo, then against the second build at the same
# path.
case_() {
  mkdir -p "_test/$1"
  printf '%s\nDefinition a := 0.\n' "$2" > "_test/$1/A.v"
  plugin labelplugin 'let note = "implementation one"'
  comp "$1"
  cp "_test/$1/A.vo" "_test/$1/first.vo"
  printf 'Require Test.A.\nDefinition b := 0.\n' > "_test/$1/B.v"
  rocq c -q -location-free-label -R "_test/$1" Test "_test/$1/B.v"
  plugin labelplugin 'let note = "implementation two"'
  comp "$1"
}

# loads DIR: coqc and rocqchk -o accept Test.B, compiled against the first
# Test.A, over the one that is there now.
loads() {
  printf 'Require Test.B.\n' > "_test/$1/C.v"
  rocq c -q -R "_test/$1" Test "_test/$1/C.v" > "_test/$1/coqc.log" 2>&1 &&
    rocqchk -silent -o -R "_test/$1" Test -norec Test.A -norec Test.B > "_test/$1/chk.log" 2>&1
}

# 1. A plain Declare ML Module of a rebuilt plugin.
case_ declare 'Declare ML Module "labelplugin".'
check "a rebuilt plugin: the .vo files differ, so the object still stores the digests" \
  differ _test/declare/first.vo _test/declare/A.vo
check "a rebuilt plugin: one label ($(label declare))" same_label declare
check "a rebuilt plugin: coqc and rocqchk accept the dependent" loads declare

# 2. A Declare ML Module under Succeed: rolled back, so the only trace is
# the ATTEMPTS record, which stores the plugin file's SHA-256.
case_ rolledback 'Succeed Declare ML Module "labelplugin".'
check "a rolled-back Declare ML Module: the record still has the SHA-256" \
  has "$("$TOOL" --attempts _test/rolledback/A.vo)" "p.cmxs sha256 [0-9a-f]\{64\}"
check "a rolled-back Declare ML Module of a rebuilt plugin: one label ($(label rolledback))" \
  same_label rolledback
check "a rolled-back Declare ML Module: coqc and rocqchk accept the dependent" loads rolledback

# 3. The plugin's name is in the key: another name, another label, although
# the two packages hold the same implementation.
plugin labelplugin2 'let note = "implementation two"'
mkdir -p _test/renamed
printf 'Declare ML Module "labelplugin2".\nDefinition a := 0.\n' > _test/renamed/A.v
comp renamed
check "another plugin name: another label" test "$(label declare)" != "$(label renamed)"

# 4. The layout version the labels above are made by (5 since D18 F1, which
#    restricted the axiom-or-opaque blinding to the library's own signature).
v=$("$TOOL" --layout-version || echo "no --layout-version")
check "--layout-version prints the layout version (got '$v')" test "$v" = "5"

exit $fail
