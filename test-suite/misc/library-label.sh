#!/usr/bin/env bash
# The location-free library label (vernac/libkeyObjects.ml, library/libkey.ml).
#
# Under -location-free-label, coqc stores the label as the digest of a library's library segment, in
# place of the MD5 of the segment's bytes. coqc and rocqchk never recompute
# that digest: they compare the copy a dependent recorded with the copy the
# dependency's file stores. So a dependent compiled against one build of a
# library loads against another build with the same label.
#
# Each variant of misc/library-label/base/A.v is compiled as the same library
# Test.A in its own directory, so even an unchanged copy moves every source
# location (the file name is part of each one). Dep.B (Require Test.A) and
# Dep.C (Require Dep.B) are compiled once, against the base. Then, against
# each variant:
# - KEEP (a rebuild elsewhere, a comment line in front, blank lines, extra
#   spaces in a tactic, a proof-only edit that creates no universe, spaces
#   and line breaks in the library attribute and the Require, and -- new in
#   label version 3, which blinds a constant's axiom-or-opaque-proof
#   distinction -- an Admitted lemma made Qed (axqed) and a Qed lemma made
#   Admitted (admitted), each of which a dependent cannot observe): coqc
#   compiles a client of Dep.C, and rocqchk -o accepts Test.A (the variant's
#   own opaque proofs), Dep.B and Dep.C;
# - CHANGE (a statement, a transparent body, an inductive, a new universe, a notation, an
#   abbreviation, a hint, a Hint Extern, an Ltac body, an Ltac
#   redefinition, a tactic notation, a Global option, an Ltac2 definition, a
#   functor declared before F, which shifts F's bound-module counter, a
#   functor declared under Succeed, which shifts it and leaves nothing
#   else, another canonical instance, an Admitted lemma made a transparent
#   Definition (axdef, a transparent body which conversion unfolds, so it is
#   NOT blinded), an Admitted lemma made Qed inside the functor F's body
#   (ftorqed) and inside the module type T (mtqed) -- label version 5 blinds
#   the axiom-or-opaque distinction only for the library's own signature,
#   since a functor application or a Declare Module copies those forms into
#   a dependent (misc/library-label-functor-flip.sh) --, a Proof-using change
#   that discharges one more section binder (secbind), and the two
#   parts of the library's summary: the Require made Require (safe), which
#   changes only which dependencies the summary lists as safe (Astra review,
#   section 3.1), and the note of the library's attribute): both refuse,
#   with their "inconsistent assumptions" messages.
# rocq-library-label --check confirms that every A.vo stores the label
# recomputed from its content ("label2" and the 32 bytes of the label, of
# which the file stores the first 16), not the MD5 of its bytes; that
# without the flag coqc stores the MD5 ("md5"), as stock does; and that a
# stored digest that is neither is "other".
#
# With STOCK_BIN set to the bin directory of a stock build of the same base
# (its rocq able to find its own worker), that build's rocq compiles the
# dependents and its rocqchk checks them: a stock coqc and rocqchk read the
# labels this coqc wrote.

set -e

export PATH=$BIN:$PATH
LOAD=${STOCK_BIN:-$BIN}

. misc/library-label-tool.inc

cd misc/library-label
rm -rf _test
mkdir _test

variant() {
  local name=$1; shift
  mkdir -p "_test/$name"
  sed "$@" base/A.v > "_test/$name/A.v"
  if cmp -s base/A.v "_test/$name/A.v" && [ "$name" != same ]; then
    echo "variant $name: the edit did not apply"; exit 1
  fi
}

KEEP="same comment blank spaces proof attrs admitted axqed"
CHANGE="stmt body inductive addcon universe notation abbrev hint extern ltac redef tacnot option ltac2 functor counter canonical axdef ftorqed mtqed secbind guard safe info"

mkdir -p _test/base
cp base/A.v _test/base/A.v
variant same -e ''
variant comment -e '1i\
(* one more line *)'
variant blank -e '1i\
\
' -e 's/^$/\n\n/'
variant spaces -e 's/intros; reflexivity/intros;   reflexivity/' -e 's/=> my_tac/=>   my_tac/'
variant proof -e 's/^Proof\. intros n\. reflexivity\. Qed\./Proof.\n  intros n.\n  exact (eq_refl (S n)).\nQed./'
variant stmt -e 's/forall n, f n = S n/forall n, f n = S (0 + n)/'
variant body -e 's/^Definition g := f\./Definition g := fun n => f n./'
variant inductive -e 's/C1 | C2/C1 | C3/'
variant addcon -e 's/^Inductive t := C1 | C2\./Inductive t := C1 | C2 | C3./'
variant universe -e '$a\
Universe label_u.'
variant notation -e 's/at level 50/at level 40/'
variant abbrev -e 's/Notation h := (f 0)/Notation h := (f 1)/'
variant hint -e 's/Hint Resolve l1/Hint Immediate l1/'
variant extern -e 's/Hint Extern 1/Hint Extern 2/'
variant ltac -e 's/intros; reflexivity/intros; simpl; reflexivity/'
variant redef -e 's/Ltac my_tac2 ::= intros\./Ltac my_tac2 ::= intros; simpl./'
variant tacnot -e 's/exact x\./apply x./'
variant option -e 's/Set Asymmetric Patterns/Unset Asymmetric Patterns/'
variant ltac2 -e 's/Ltac2 l2 (n : int) := n\./Ltac2 l2 (n : int) := (n, n)./'
variant functor -e 's/^Module F (X : S)/Module F0 (X0 : S). End F0.\nModule F (X : S)/'
variant counter -e 's/^Module F (X : S)/Succeed Module F0 (X0 : S) := X0.\nModule F (X : S)/'
variant attrs -e 's/^Attributes warn(note=/Attributes  warn(\n  note=/' -e 's/^Require Corelib/Require\n  Corelib/'
variant canonical -e 's/^Canonical Structure cs_nat\./Canonical Structure cs_nat2./'
variant admitted -e 's/^Proof\. intros n\. reflexivity\. Qed\./Proof. intros n. reflexivity. Admitted./'
variant axqed -e 's/^Admitted\.$/Proof. exact I. Qed./'
variant axdef -e 's/^Lemma lax : True\.$/Definition lax := I./' -e '/^Admitted\.$/d'
variant ftorqed -e 's/Lemma fc : True\. Admitted\./Lemma fc : True. Proof. exact I. Qed./'
variant mtqed -e 's/Lemma tc : True\. Admitted\./Lemma tc : True. Proof. exact I. Qed./'
variant secbind -e 's/Proof using sv\./Proof using sv sw./'
variant guard -e 's/^Fixpoint fg /Unset Guard Checking.\nFixpoint fg /'
variant safe -e 's/^Require Corelib\.Classes\.CMorphisms\./Require (safe) Corelib.Classes.CMorphisms./'
variant info -e 's/note="label fixture"/note="label fixture, changed"/'

for v in base $KEEP $CHANGE; do
  rocq c -q -location-free-label -R "_test/$v" Test "_test/$v/A.v"
done
mkdir -p _test/noflag
cp base/A.v _test/noflag/A.v
rocq c -q -R _test/noflag Test _test/noflag/A.v

fail=0
labels=0
for v in base $KEEP $CHANGE; do
  c=$("$TOOL" --check "_test/$v/A.vo")
  s=$("$TOOL" --stored "_test/$v/A.vo")
  if [[ $c =~ ^label2\ ([0-9a-f]{64})$ ]] && [ "${BASH_REMATCH[1]:0:32}" = "$s" ]; then labels=$((labels + 1))
  else echo "FAIL $v: A.vo does not store the first 16 bytes of its label: $c (stored $s)"; fail=1; fi
done
if [ "$labels" = "$(wc -w <<< "base $KEEP $CHANGE")" ]; then
  echo "PASS all $labels A.vo files compiled with the flag store the first 16 bytes of their label"
fi
# With a stock build: the same file at the same path, compiled by stock and
# by this coqc without the flag, gives the same bytes.
if [ -n "${STOCK_BIN:-}" ]; then
  cp _test/noflag/A.vo _test/noflag/A.vo.fork
  "$STOCK_BIN"rocq c -q -R _test/noflag Test _test/noflag/A.v
  if cmp -s _test/noflag/A.vo _test/noflag/A.vo.fork; then
    echo "PASS without the flag, A.vo is byte-identical to stock's"
  else echo "FAIL without the flag, A.vo differs from stock's"; fail=1; fi
fi
c=$("$TOOL" --check _test/noflag/A.vo)
if [[ $c =~ ^md5\ [0-9a-f]{32}$ ]] && [ "$c" = "md5 $("$TOOL" --stored _test/noflag/A.vo)" ]; then
  echo "PASS without the flag, A.vo stores the MD5 of its bytes"
else echo "FAIL without the flag, A.vo does not store the MD5 of its bytes: $c"; fail=1; fi
# A stored digest that is neither the label nor the MD5 (a label of another
# layout version, say): both copies of the library segment's digest set to
# 16 bytes 0xab (layout per lib/objFile.ml).
python3 - _test/base/A.vo _test/other.vo <<'PY'
import struct, sys
b = bytearray(open(sys.argv[1], 'rb').read())
(sp,) = struct.unpack_from(">Q", b, 8)
(n,) = struct.unpack_from(">I", b, sp); off = sp + 4
for _ in range(n):
    (ln,) = struct.unpack_from(">I", b, off); off += 4
    name = bytes(b[off:off+ln]); off += ln
    pos, sz = struct.unpack_from(">QQ", b, off); off += 16
    if name == b"library":
        b[off:off+16] = b"\xab" * 16
        b[pos+sz:pos+sz+16] = b"\xab" * 16
    off += 16
open(sys.argv[2], 'wb').write(b)
PY
c=$("$TOOL" --check _test/other.vo)
if [ "$c" = "other $(printf 'ab%.0s' {1..16})" ]; then echo "PASS another stored digest is \"other\""
else echo "FAIL another stored digest: $c"; fail=1; fi

mkdir -p _test/dep
printf 'Require Test.A.\nDefinition b := Test.A.g.\n' > _test/dep/B.v
printf 'Require Dep.B.\nDefinition c := Dep.B.b.\n' > _test/dep/C.v
printf 'Require Dep.C.\nDefinition d := Dep.C.c.\n' > _test/dep/D.v
"$LOAD"rocq c -q -R _test/base Test -R _test/dep Dep _test/dep/B.v
"$LOAD"rocq c -q -R _test/base Test -R _test/dep Dep _test/dep/C.v

# coqc VARIANT: "ok", or "refused" with coqc's message.
coqc_against() {
  if "$LOAD"rocq c -q -R "_test/$1" Test -R _test/dep Dep _test/dep/D.v > _test/coqc.log 2>&1; then
    echo ok
  elif grep -q "makes inconsistent assumptions over library Test.A" _test/coqc.log; then
    echo refused
  else
    echo error; cat _test/coqc.log >&2
  fi
}
# rocqchk VARIANT: "ok", or "refused" with rocqchk's message.
rocqchk_against() {
  if "$LOAD"rocqchk -silent -o -R "_test/$1" Test -R _test/dep Dep \
       -norec Test.A -norec Dep.B -norec Dep.C > _test/chk.log 2>&1; then
    echo ok
  elif grep -q "Inconsistent assumptions over module Test.A" _test/chk.log; then
    echo refused
  else
    echo error; cat _test/chk.log >&2
  fi
}
expect() {
  local want=$1 v=$2 got
  got=$(coqc_against "$v")
  if [ "$got" = "$want" ]; then echo "PASS coqc against $v: $got"
  else echo "FAIL coqc against $v: $got, expected $want"; fail=1; fi
  got=$(rocqchk_against "$v")
  if [ "$got" = "$want" ]; then echo "PASS rocqchk -o against $v: $got"
  else echo "FAIL rocqchk -o against $v: $got, expected $want"; fail=1; fi
}

expect ok base
for v in $KEEP; do expect ok "$v"; done
for v in $CHANGE; do expect refused "$v"; done

exit $fail
