#!/usr/bin/env bash
# ROCQ_ASSUMPTIONS_SHARED_DIR shares Print Assumptions entries between the
# processes that name one directory. Every query must print, with sharing,
# what it prints without it:
#
# - fresh:      Q1 alone, in an empty directory;
# - reused:     Q2 and Q3 after Q1 filled the directory, so they read its
#               entries (the debug counter of entries READ FROM THE DIRECTORY,
#               which is apart from the count of entries the process already
#               had, must be above zero);
# - concurrent: Q1, Q2 and Q3 at once, in an empty directory, where they must
#               also share: between them they must read entries from the
#               directory, or wait for an object another of them claimed;
# - changed:    the negative control. Lib is compiled again with top1 proved
#               from the axiom lib_ax, and Q1 runs with the directory the old
#               Lib filled. Its entries for Lib's objects must not be read,
#               since the library changed: Q1 must name lib_ax, as without
#               sharing, and it must still read the entries of Base, which did
#               not change;
# - damaged:    in a directory Q1 filled, one entry is emptied, one is cut to
#               half its length, one has one byte in its middle flipped, and
#               one is deleted while its claim stays, which is what a
#               claimant that was killed during its walk leaves. Q1 must read
#               none of them, take over each claim at once (the system freed
#               the claimants' locks) instead of waiting, and walk the four
#               objects itself;
# - replaced:   a Require that fails because the file it finds holds another
#               library replaces that library's opaque proofs. A process that
#               filled the directory before the replacement must not answer
#               the later query from its entries: a replaced table's proofs
#               come from a file whose own dependencies the loaded library
#               does not record, so no object of such a library is shared.
#               Both arms must print what Rocq without the directory prints.
# - labelled:   a library compiled with -location-free-label records its
#               LABEL as the digest of its declarations, and the label is
#               equal across an edit that swaps which of two lemmas is
#               Admitted and which is proved. Two such libraries also carry
#               the same opaque table, since the table holds the proof and
#               not the name it is under, so a key built from the recorded
#               digests would be the same for both and the second query
#               would print the first's answer. No library whose recorded
#               digest is not the MD5 of its declarations is shared
#               (vernac/library.ml, [label_digested]), so both arms print
#               what Rocq without the directory prints.
# - unusable:   a directory that cannot be created turns sharing off.
#
# Q3 also queries objects of the file being compiled, inside and outside a
# section, which are never shared.

set -e

export PATH=$BIN:$PATH
export LC_ALL=C

cd misc/print-assumptions-shared
rm -rf _test
mkdir -p _test
cp Base.v Lib.v Q1.v Q2.v Q3.v _test
cd _test

rc() { rocq c -q -R . S -native-compiler no "$@"; }

rc Base.v
rc Lib.v
for q in Q1 Q2 Q3; do rc $q.v > $q.plain.out; done

status=0

# [shared <dir> <file> <label>]: compiles <file> sharing <dir>; keeps stdout
# and the debug lines.
shared() {
  ROCQ_ASSUMPTIONS_SHARED_DIR=$1 ROCQ_DEBUG_ASSUMPTIONS_SHARED=1 rc "$2.v" > "$2.$3.out" 2> "$2.$3.err"
  grep -v '^\[assumptions-shared\] ' "$2.$3.err" > "$2.$3.other.err" || true
  diff -u /dev/null "$2.$3.other.err"
}

# [count <field> <file> <label>]: the sum of a debug counter over the queries.
count() {
  grep -o "$1 [0-9]*" "$2.$3.err" | awk '{ s += $NF } END { print s + 0 }'
}

mkdir fresh
shared fresh Q1 fresh
diff -u Q1.plain.out Q1.fresh.out
[ "$(count walked Q1 fresh)" -gt 0 ] || { echo "fresh: Q1 walked nothing"; status=1; }
# A copy of the directory only Q1 filled, for the damaged case.
cp -r fresh damaged

for q in Q2 Q3; do
  shared fresh $q reused
  diff -u $q.plain.out $q.reused.out
  reads=$(count read $q reused)
  echo "reused: $q read $reads entries"
  [ "$reads" -gt 0 ] || { echo "reused: $q read no entry, so the case tests no sharing"; status=1; }
done

mkdir concurrent
shared concurrent Q1 concurrent & p1=$!
shared concurrent Q2 concurrent & p2=$!
shared concurrent Q3 concurrent & p3=$!
wait $p1; wait $p2; wait $p3
shares=0
for q in Q1 Q2 Q3; do
  diff -u $q.plain.out $q.concurrent.out
  shares=$(( shares + $(count read $q concurrent) + $(count put-aside $q concurrent) ))
done
echo "concurrent: $shares entries read from the directory or objects waited for"
[ "$shares" -gt 0 ] || { echo "concurrent: the three processes shared nothing"; status=1; }

cp ../changed/Lib.v Lib.v
rc Lib.v
rc Q1.v > Q1.changed.plain.out
if diff -q Q1.plain.out Q1.changed.plain.out > /dev/null; then
  echo "changed: Lib's change does not change Q1's output, so the control tests nothing"
  status=1
fi
shared fresh Q1 changed
diff -u Q1.changed.plain.out Q1.changed.out
reads=$(count read Q1 changed)
walked=$(count walked Q1 changed)
echo "changed: Q1 read $reads entries and walked $walked objects"
[ "$reads" -gt 0 ] || { echo "changed: Q1 read no entry of Base"; status=1; }
[ "$walked" -gt 0 ] || { echo "changed: Q1 walked nothing, so it read entries of the old Lib"; status=1; }

cp ../Lib.v Lib.v
rc Lib.v
set -- $(ls damaged/entries/*/* | grep -v '\.claim$')
: > "$1"
n=$(wc -c < "$2"); head -c $((n / 2)) "$2" > cut.tmp; mv cut.tmp "$2"
n=$(wc -c < "$3"); off=$((n / 2))
b=$(od -An -tu1 -j $off -N1 "$3" | tr -d ' ')
printf "\\$(printf '%03o' $((b ^ 1)))" | dd of="$3" bs=1 seek=$off conv=notrunc 2> /dev/null
rm "$4"
[ -e "$4.claim" ] || { echo "damaged: no claim beside $4"; status=1; }
shared damaged Q1 damaged
diff -u Q1.plain.out Q1.damaged.out
taken=$(count taken-over Q1 damaged)
echo "damaged: Q1 took over $taken claims"
[ "$taken" -eq 4 ] || { echo "damaged: expected 4 claims taken over"; status=1; }

# [set -e] is off inside this subshell too, since its status is tested, so
# each step that can fail ends the case itself.
(
  mkdir -p replaced && cd replaced || exit 1
  cp -r ../../replaced/first ../../replaced/second ../../replaced/Main.v . || exit 1
  cp Main.v first/ || exit 1
  rocq c -q -native-compiler no -Q first "" first/Y.v || exit 1
  rocq c -q -native-compiler no -Q second "" second/Y.v || exit 1
  cp second/Y.vo first/X.vo || exit 1
  rocq c -q -native-compiler no -Q first "" first/Main.v > Main.plain.out 2> Main.plain.err \
    || { echo "replaced: the query without a directory failed"; exit 1; }
  diff -u /dev/null Main.plain.err || exit 1
  mkdir -p D || exit 1
  # a process that queries Y before any replacement fills the directory
  printf 'Require Y.\nPrint Assumptions Y.c.\n' > first/Fill.v
  ROCQ_ASSUMPTIONS_SHARED_DIR="$PWD/D" \
    rocq c -q -native-compiler no -Q first "" first/Fill.v > Fill.out 2> Fill.err \
    || { echo "replaced: the query that fills the directory failed"; exit 1; }
  ROCQ_DEBUG_ASSUMPTIONS_SHARED=1 ROCQ_ASSUMPTIONS_SHARED_DIR="$PWD/D" \
    rocq c -q -native-compiler no -Q first "" first/Main.v > Main.shared.out 2> Main.shared.err \
    || { echo "replaced: the query with the directory failed"; exit 1; }
  diff -u Main.plain.out Main.shared.out \
    || { echo "replaced: the query answered from entries of the replaced table"; exit 1; }
  grep -v '^\[assumptions-shared\] ' Main.shared.err > Main.shared.other.err || true
  diff -u /dev/null Main.shared.other.err || exit 1
  echo "replaced: the query answered the same with a directory filled before the replacement"
) || status=1

# [set -e] is off inside this subshell, since its status is tested, so each
# step that can fail ends the case itself.
(
  mkdir -p labelled && cd labelled || exit 1
  mkdir -p a1 a2 q1 q2 q3 q4 D || exit 1
  printf 'Lemma a : True.\nAdmitted.\nLemma b : True.\nProof. exact I. Qed.\n' > a1/A.v
  printf 'Lemma a : True.\nProof. exact I. Qed.\nLemma b : True.\nAdmitted.\n' > a2/A.v
  lc() { rocq c -q -native-compiler no -location-free-label "$@"; }
  lc -R a1 "" a1/A.v || { echo "labelled: a1 did not compile"; exit 1; }
  lc -R a2 "" a2/A.v || { echo "labelled: a2 did not compile"; exit 1; }
  # The two labels must be equal, or the case tests nothing.
  l1=$("${BIN}rocq-library-label" --check a1/A.vo) || exit 1
  l2=$("${BIN}rocq-library-label" --check a2/A.vo) || exit 1
  [ "$l1" = "$l2" ] || { echo "labelled: the two libraries have different labels ($l1, $l2)"; exit 1; }
  printf 'Require A.\nPrint Assumptions A.b.\n' > q1/Q.v
  for q in q2 q3 q4; do cp q1/Q.v $q/Q.v || exit 1; done
  lc -R a1 "" -R q1 Q1 q1/Q.v > plain1.out || { echo "labelled: the query of a1 failed"; exit 1; }
  lc -R a2 "" -R q2 Q2 q2/Q.v > plain2.out || { echo "labelled: the query of a2 failed"; exit 1; }
  if diff -q plain1.out plain2.out > /dev/null; then
    echo "labelled: the two libraries give one answer, so the case tests nothing"
    exit 1
  fi
  # One directory, the first library's query first.
  ROCQ_ASSUMPTIONS_SHARED_DIR="$PWD/D" lc -R a1 "" -R q3 Q3 q3/Q.v > shared1.out \
    || { echo "labelled: the shared query of a1 failed"; exit 1; }
  ROCQ_ASSUMPTIONS_SHARED_DIR="$PWD/D" lc -R a2 "" -R q4 Q4 q4/Q.v > shared2.out \
    || { echo "labelled: the shared query of a2 failed"; exit 1; }
  diff -u plain1.out shared1.out || { echo "labelled: a1's query changed with the directory"; exit 1; }
  diff -u plain2.out shared2.out \
    || { echo "labelled: a2's query answered for a1, the library with the same label"; exit 1; }
  echo "labelled: each query answered for its own library"
) || status=1

shared "$PWD/missing/dir" Q1 unusable
diff -u Q1.plain.out Q1.unusable.out
grep -q 'sharing off' Q1.unusable.err || { echo "unusable: sharing stayed on"; status=1; }

exit $status
