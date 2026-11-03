#!/usr/bin/env bash
# A compiled file must not depend on when the garbage collector runs
# (Hashset.retain_entries, rocq-prover/rocq#17207 and #22703). The same file is
# compiled under five GC settings, which move every collection point, and the
# .vo files must be equal byte for byte. Without retain_entries the VM block
# table forgets a block whenever a collection reclaims it, so the vmlibrary
# segment of this file differs under each setting (five different files on
# Rocq 9.2, measured).

D=misc/tmp_vo_reproducible_gc
rm -rf "$D" && mkdir -p "$D" && cd "$D" || exit 1
cat > R.v <<'EOF'
Fixpoint rep (n : nat) (x : nat) : list nat :=
  match n with O => nil | S n => cons x (rep n x) end.
Definition big := Eval vm_compute in rep (Nat.mul 100 200) 50.
EOF
# rep 20000 is a deep term: give the compiles the stack that its marshalling needs.
ulimit -s unlimited 2>/dev/null || ulimit -s 1048576
first=
for p in s=256k s=1M s=2M s=4M,o=80 s=32M,o=200; do
  rm -f R.vo R.glob
  OCAMLRUNPARAM=$p $coqc -q -Q . R R.v || { echo "compile failed under OCAMLRUNPARAM=$p"; exit 1; }
  sum=$(cksum < R.vo)
  if [ -z "$first" ]; then first=$sum
  elif [ "$sum" != "$first" ]; then
    echo "R.vo differs under OCAMLRUNPARAM=$p ($sum) from s=256k ($first)"; exit 1
  fi
done
cd ../.. && rm -rf "$D"
exit 0
