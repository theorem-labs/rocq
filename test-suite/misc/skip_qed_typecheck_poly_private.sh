#!/usr/bin/env bash
# A universe-polymorphic Qed proof whose body adds private universes and
# constraints, not typed by the kernel (-skip-qed-typecheck). The private
# constraints of [private_transitivity] relate its private universe to its
# bound universes [i] and [j], so they must be stored over the bound
# universes, as for a checked proof, for rocqchk to accept the library.
set -euo pipefail

export PATH="$BIN:$PATH"
workdir=$(mktemp -d)
trap 'rm -rf "$workdir"' EXIT

cat > "$workdir/poly_private.v" <<'EOF'
Set Universe Polymorphism.

(* Private universes, with constraints between private universes only. *)
Lemma internal_qed@{i j | i <= j} (A : Type@{i}) : Type@{j}.
Proof.
  pose (foo := Type).
  exact A.
Qed.

(* Private constraints that mention the bound universes: i < k < j. *)
Unset Strict Universe Declaration.
Lemma private_transitivity@{i j} (A : Type@{i}) : Type@{j}.
Proof.
  pose (bar := Type : Type@{j}).
  pose (foo := Type@{i} : bar).
  exact bar.
Qed.

Definition private_transitivity'@{i j | i < j} := private_transitivity@{i j}.
Fail Definition dummy@{i j | j <= i +} := private_transitivity@{i j}.
EOF

for option in "" "-skip-qed-typecheck"; do
  rm -f "$workdir"/poly_private.{vo,vos,vok,glob}
  rocq c -q $option -R "$workdir" Top "$workdir/poly_private.v" ||
    { echo "rocq c failed ${option:-without option}" >&2; exit 1; }
  rocqchk -silent -R "$workdir" Top -norec Top.poly_private ||
    { echo "rocqchk rejected the library built ${option:-without option}" >&2; exit 1; }
done
