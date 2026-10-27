#!/usr/bin/env bash
# Two builds of the same sources give the same library labels.
#
# A reader that keeps a library across two builds compares their labels, so
# the label must be computed from what the library holds and from nothing a
# build can vary: not the process, the time, the heap layout or how the
# marshaller shares values. The stored digest of a stock build (the MD5 of
# the library segment's bytes) can differ between two builds of the same
# sources when the garbage collector changes what is shared in memory; the
# label is computed by a canonical encoding that does not see sharing
# (library/libkey.ml), so it must not.
#
# misc/library-label/base/A.v (an object of each kind the label strips
# locations from, a functor, a library attribute, a Require) and two
# dependents (B requires A, C requires B) are compiled three times, each from
# a cold start in its own directory, under three settings of the OCaml
# runtime (the default, a small minor heap, and a much lazier major GC).
# Every build must give each library the label of the first build, and a
# dependent of one build must load over the libraries of another.

set -e

export PATH=$BIN:$PATH

. misc/library-label-tool.inc

mkdir -p misc/library-label-reproducible
cd misc/library-label-reproducible
rm -rf _test
mkdir _test
fail=0

label() { "$TOOL" --check "$1" | awk '$1 == "label2" { print $2 }'; }

# build NAME OCAMLRUNPARAM: the three libraries, from a cold start, in
# _test/NAME, at one logical path.
build() {
  local d=_test/$1
  mkdir -p "$d/test" "$d/dep"
  cp ../library-label/base/A.v "$d/test/A.v"
  printf 'Require Test.A.\nDefinition b := Test.A.f 1.\n' > "$d/dep/B.v"
  printf 'Require Dep.B.\nDefinition c := Dep.B.b.\n' > "$d/dep/C.v"
  for f in test/A dep/B dep/C; do
    OCAMLRUNPARAM=$2 rocq c -q -location-free-label -R "$d/test" Test -R "$d/dep" Dep "$d/$f.v" \
      || { echo "FAIL build $1: $f.v did not compile"; exit 1; }
  done
}

build default ""
build small_minor "s=4k"
build lazy_major "o=1000,s=1M"

for f in test/A dep/B dep/C; do
  first=$(label "_test/default/$f.vo")
  check "build default: $f.vo stores a label ($first)" test -n "$first"
  for b in small_minor lazy_major; do
    other=$(label "_test/$b/$f.vo")
    check "build $b: $f.vo has the label of build default ($other)" test "$other" = "$first"
  done
done

# The stored digests are what a dependent records and what coqc compares
# when it loads: C of one build loads over A and B of another.
mkdir -p _test/mixed/test _test/mixed/dep
cp _test/small_minor/test/A.vo _test/mixed/test/
cp _test/lazy_major/dep/B.vo _test/default/dep/C.vo _test/mixed/dep/
printf 'Require Dep.C.\nDefinition d := Dep.C.c.\n' > _test/mixed/D.v
check "a dependent loads over the libraries of other builds" \
  rocq c -q -R _test/mixed/test Test -R _test/mixed/dep Dep _test/mixed/D.v

exit $fail
