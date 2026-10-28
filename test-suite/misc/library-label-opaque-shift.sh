#!/usr/bin/env bash
# S3 (D18, dispatch://INFRA-361; Astra review 2 §1.2, Claude review S3): a foreign
# opaque reference survives a functor APPLICATION (an Include copies the proof locally
# and holds no foreign reference, but applying another library's functor keeps an
# Indirect into that library's opaque table, as Astra §3.3 noted). Label v2b drops the
# opaque table index that reference carries, so an edit that shifts the index leaves
# the owner's label equal -- which the keep rule's byte-identity guard over the
# referenced owner has to catch, because the label cannot.
#
# A has an EARLIER lemma `extra` (Admitted, so NOT in A's opaque table), a functor F
# whose body has an opaque lemma `t` (Qed), and a module A0. B does `Module R := F A0`,
# so B's instantiated `t` holds an Indirect into A's opaque table at F.t's index. The
# `shift` variant turns `extra` from Admitted into a Qed proof: `extra` takes an opaque
# slot and F.t's index moves, so B's stored Indirect would read the wrong proof.
#
# Under label v2b (version 3) A's label is EQUAL across that edit (the blinding drops
# the body form AND the index): this asserts that equality (RED on a pre-v2b build,
# where the edit changes A's label; GREEN on v2b), shows A's object bytes DIFFER, and
# shows B's --axiom-report-json names A as a foreign opaque owner -- the evidence the
# keep rule uses to deny keeping B (A is referenced and not byte-identical).

set -e
export PATH=$BIN:$PATH

TOOL=${LIBRARY_LABEL:-}
for t in "${BIN}rocq-library-label" "$PWD/../_build/default/checker/library_label.exe"; do
  if [ -z "$TOOL" ] && [ -x "$t" ]; then TOOL=$t; fi
done
[ -n "$TOOL" ] || { echo "FAIL no rocq-library-label on PATH or BIN"; exit 2; }

cd misc
rm -rf _oshift
mkdir -p _oshift/base _oshift/shift _oshift/b _oshift/b2

body='Module Type S. Parameter u : True. End S.
Module F (X : S).
  Lemma t : True. Proof. exact X.u. Qed.
End F.
Module A0 : S. Definition u := I. End A0.'

{ printf 'Lemma extra : True.\nAdmitted.\n'; printf '%s\n' "$body"; } > _oshift/base/A.v
{ printf 'Lemma extra : True.\nProof. exact I. Qed.\n'; printf '%s\n' "$body"; } > _oshift/shift/A.v
printf 'Require A.\nModule R := A.F A.A0.\n' > _oshift/b/B.v
cp _oshift/b/B.v _oshift/b2/B.v

rocq c -q -location-free-label -R _oshift/base A _oshift/base/A.v
rocq c -q -location-free-label -R _oshift/shift A _oshift/shift/A.v
rocq c -q -location-free-label -R _oshift/base A -R _oshift/b Bdep _oshift/b/B.v
rocq c -q -location-free-label -R _oshift/shift A -R _oshift/b2 Bdep _oshift/b2/B.v

fail=0
label() { "$TOOL" --check "$1" | awk '{print $2}'; }
alib=$("$TOOL" --axiom-report-json _oshift/base/A.vo | sed -n 's/.*"library":"\([^"]*\)".*/\1/p')

la=$(label _oshift/base/A.vo)
lb=$(label _oshift/shift/A.vo)
if [ "$la" = "$lb" ]; then
  echo "PASS v2b: A's label is equal across extra Admitted->Qed, though its opaque table shifted ($la)"
else
  echo "FAIL A's label differs across the shift (RED on a pre-v2b build): $la vs $lb"; fail=1
fi

if cmp -s _oshift/base/A.vo _oshift/shift/A.vo; then
  echo "FAIL A's object bytes are identical across the shift (the edit should change the object)"; fail=1
else
  echo "PASS A's object bytes differ across the shift (so a byte-identity guard on A denies the keep)"
fi

# B's instantiated t is an Indirect into A's opaque table, so the report names A as a
# foreign opaque owner -- the keep rule's foreign-opaque/copied-from coverage then
# requires A byte-identical, which the shift breaks.
bfor=$("$TOOL" --axiom-report-json _oshift/b/B.vo | sed -n 's/.*"foreign_opaque_libraries":\(\[[^]]*\]\).*/\1/p')
if printf '%s' "$bfor" | grep -q "\"$alib\""; then
  echo "PASS B's --axiom-report-json names A ($alib) as a foreign opaque owner: $bfor"
else
  echo "FAIL B's report does not name A ($alib) as a foreign opaque owner: $bfor"; fail=1
fi

lba=$(label _oshift/b/B.vo)
lbb=$(label _oshift/b2/B.vo)
if [ "$lba" = "$lbb" ]; then
  echo "PASS v2b: B's own label is equal whether its instantiated copy points at A's old or shifted table ($lba)"
else
  echo "INFO B's label differs ($lba vs $lbb) -- the functor instance carried a label-visible difference"
fi

exit $fail
