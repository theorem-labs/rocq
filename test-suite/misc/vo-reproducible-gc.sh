#!/usr/bin/env bash
# A compiled file must not depend on when the garbage collector runs
# (Hashset.retain_entries, rocq-prover/rocq#17207 and #22703). Each file is
# compiled under five GC settings, which move every collection point, and its
# .vo files must be equal byte for byte. Without retain_entries, on Rocq 9.2:
# - S.v (bugs/bug_3513.v, setoid rewriting): the library segment under
#   s=32M,o=200 differs from the one under s=256k, in the sharing of the
#   identifiers that the hash-consing tables answered with a dead copy.
# - R.v: the VM block table forgets a block whenever a collection reclaims it,
#   so the vmlibrary segment differs under each setting.

D=misc/vo-reproducible-gc/_test
rm -rf "$D" && mkdir -p "$D" || exit 1
cp bugs/bug_3513.v "$D/S.v" || exit 1
cat > "$D/R.v" <<'EOF'
Fixpoint rep (n : nat) (x : nat) : list nat :=
  match n with O => nil | S n => cons x (rep n x) end.
Definition big := Eval vm_compute in rep (Nat.mul 100 200) 50.
EOF
# rep 20000 is a deep term: give the compiles the stack that its marshalling needs.
ulimit -s unlimited 2>/dev/null || ulimit -s 1048576
for f in S R; do
  for p in s=256k s=1M s=2M s=4M,o=80 s=32M,o=200; do
    rm -f "$D/$f.vo"
    OCAMLRUNPARAM=$p $coqc -R "$D" T "$D/$f.v" || { echo "$f.v: compile failed under OCAMLRUNPARAM=$p"; exit 1; }
    if [ ! -f "$D/$f.first.vo" ]; then cp "$D/$f.vo" "$D/$f.first.vo"
    elif ! cmp "$D/$f.first.vo" "$D/$f.vo"; then
      echo "$f.vo under OCAMLRUNPARAM=$p differs from $f.vo under s=256k"; exit 1
    fi
  done
done
rm -rf misc/vo-reproducible-gc
