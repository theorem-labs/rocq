#!/usr/bin/env bash
# A compiled file must not depend on when the garbage collector runs
# (Hashset.retain_entries, rocq-prover/rocq#17207 and #22703). The same file is
# compiled under five GC settings, which move every collection point, and the
# .vo files must be equal byte for byte. Without retain_entries the VM block
# table forgets a block whenever a collection reclaims it, so the vmlibrary
# segment of this file differs under each setting (five different files on
# Rocq 9.2, measured).

D=misc/vo-reproducible-gc/_test
rm -rf "$D" && mkdir -p "$D" || exit 1
cat > "$D/R.v" <<'EOF'
Fixpoint rep (n : nat) (x : nat) : list nat :=
  match n with O => nil | S n => cons x (rep n x) end.
Definition big := Eval vm_compute in rep (Nat.mul 100 200) 50.
EOF
# rep 20000 is a deep term: give the compiles the stack that its marshalling needs.
ulimit -s unlimited 2>/dev/null || ulimit -s 1048576
for p in s=256k s=1M s=2M s=4M,o=80 s=32M,o=200; do
  rm -f "$D/R.vo"
  OCAMLRUNPARAM=$p $coqc -R "$D" R "$D/R.v" || { echo "compile failed under OCAMLRUNPARAM=$p"; exit 1; }
  if [ ! -f "$D/first.vo" ]; then cp "$D/R.vo" "$D/first.vo"
  elif ! cmp "$D/first.vo" "$D/R.vo"; then
    echo "R.vo under OCAMLRUNPARAM=$p differs from R.vo under s=256k"; exit 1
  fi
done
rm -rf misc/vo-reproducible-gc
