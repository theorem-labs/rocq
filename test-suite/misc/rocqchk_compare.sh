#!/usr/bin/env bash
# shellcheck disable=SC2154 # BIN and coqc are set by the misc rule of test-suite/Makefile

# rocqchk -compare compares a solution with a challenge: two trees of .vo
# files compiled from the same file names under the same root, Top. Each run
# checks rocqchk's exit status, whether the verdict file exists, the verdict
# of each theorem, and, for a run that rocqchk refuses, its error. The rules
# are those of the section "Comparing a solution with a challenge" of the
# rocqchk documentation.
#
# The files are compiled with -noinit, so a proof is a term, and a solution
# often gives as a Definition a theorem that the challenge leaves open.

set -eu

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

out=$d/verdict.json
log=$d/log
: > "$log"
# A verdict file that says pass, as an earlier run would leave it. Every
# refused run starts with it in place and must remove it.
stale='{"format":1,"theorems":[{"name":"Top.A.thm","verdict":"pass","reason":"","axioms":[],"flags":[]}],"declarations":[],"admitted":[]}'

fail() {
  echo "FAILURE: $*"
  cat "$log"
  if [ -f "$out" ]; then cat "$out"; fi
  exit 1
}

# Write <tree>/<file> from the standard input and compile it, with <tree>
# bound to Top.
compile() { # <tree> <file> [rocq c options]
  local tree=$d/$1 file=$d/$1/$2
  shift 2
  mkdir -p "$(dirname "$file")"
  cat > "$file"
  $coqc -noinit -native-compiler no -Q "$tree" Top "$@" "$file"
}

digest() { "$BIN"rocqchk -sha256 "$d/$1"; }

chk() { "$BIN"rocqchk -silent "$@" > "$log" 2>&1; }

# Compare the libraries at the top of the solution tree <tree> with the
# challenge of its case, <case>/ch.
compare() { # <tree> <config> [rocqchk options]
  local tree=$d/$1 config=$d/$2 ch=$d/${1%%/*}/ch libs=() f
  shift 2
  for f in "$tree"/*.vo; do libs+=("Top.$(basename "$f" .vo)"); done
  chk -Q "$tree" Top "$@" -compare "$config" -challenge "$ch" -compare-out "$out" "${libs[@]}"
}

# The verdict file is there and holds each <text>; <run> names the run in a
# failure.
holds() { # <run> <text>...
  local run=$1 text
  shift
  [ -f "$out" ] || fail "$run: no verdict file"
  for text in "$@"; do
    grep -qF -- "$text" "$out" || fail "$run: the verdict does not hold $text"
  done
}

# A run of compare that writes a verdict: it exits 0 and the verdict file
# holds each <text>.
verdict() { # <tree> <config> <text>...
  local run="$1 with $2"
  ran "$run" compare "$1" "$2"
  shift 2
  holds "$run" "$@"
}

lacks() { # <text>
  if grep -qF -- "$1" "$out"; then fail "the verdict holds $1"; fi
}

# A run that rocqchk refuses: it exits non-zero, the stale verdict file is
# gone, and the error holds <text>.
refused() { # <text> <command>...
  local text=$1
  shift
  printf '%s\n' "$stale" > "$out"
  if "$@"; then fail "$*: not refused"; fi
  [ ! -e "$out" ] || fail "$*: the stale verdict file is still there"
  grep -qF -- "$text" "$log" || fail "$*: the error does not hold $text"
}

# A run that writes a verdict: <command> exits 0, with no verdict file in
# place before it; <run> names the run in a failure.
ran() { # <run> <command>...
  local run=$1
  shift
  rm -f "$out"
  "$@" || fail "$run: exit $?"
}

in_dir() { (cd "$1" && shift && "$@"); }

# The config of a case whose challenge is A.v, with the theorem Top.A.thm.
config() { # <case> [<member>,]
  cat <<EOF
{"theorems": [{"name": "Top.A.thm"}], ${2:-}
 "challenge_files": [{"path": "A.vo", "sha256": "$(digest "$1/ch/A.vo")"}]}
EOF
}

#### The main challenge: definitions in Defs.v, and two theorems in A.v
#### whose proofs are left out.

compile main/ch Defs.v <<'EOF'
Definition prop_id := forall A : Prop, forall _ : A, A.
(* A name that the verdict file writes escaped. *)
Definition théorème_ÿ := prop_id.
Polymorphic Definition pid@{u} (A : Type@{u}) (a : A) : A := a.
Module Type SIG.
  Parameter P : Prop.
End SIG.
Module M <: SIG.
  Definition P := prop_id.
End M.
Module F (X : SIG).
  Definition Q := X.P.
End F.
Module FM := F M.
EOF
compile main/ch A.v <<'EOF'
Require Import Top.Defs.
Theorem thm : théorème_ÿ.
Proof. Admitted.
Theorem other : prop_id.
Proof. Admitted.
EOF

main_config() { # [<member>,]
  cat <<EOF
{"theorems": [{"name": "Top.A.thm"}, {"name": "Top.A.other"}], ${1:-}
 "challenge_files": [{"path": "Defs.vo", "sha256": "$(digest main/ch/Defs.vo)"},
                     {"path": "A.vo", "sha256": "$(digest main/ch/A.vo)"}]}
EOF
}
main_config > "$d/main.json"
main_config '"rewrite_rules": true,' > "$d/main-rules.json"

# A solution: the challenge's Defs.v, and an A.v read from the standard input.
solution() { # <tree> [rocq c options]
  local tree=$1
  shift
  compile "$tree" Defs.v "$@" < "$d/main/ch/Defs.v"
  compile "$tree" A.v "$@"
}

solution main/honest <<'EOF'
Require Import Top.Defs.
Definition thm : théorème_ÿ := fun A a => a.
Definition other : prop_id := thm.
EOF
# The whole verdict file. No library is given with -admit.
verdict main/honest main.json \
  '{"format":1,"theorems":[{"name":"Top.A.thm","verdict":"pass","reason":"","axioms":[],"flags":[]},' \
  '{"name":"Top.A.other","verdict":"pass","reason":"","axioms":[],"flags":[]}],"declarations":[],"admitted":[]}'
# A run as one that checks with the bytecode compiler on, which compiles the
# VM code of each constant it checks, gives the same verdict.
ran 'main/honest with -bytecode-compiler yes' compare main/honest main.json -bytecode-compiler yes
holds 'main/honest with -bytecode-compiler yes' \
  '"name":"Top.A.thm","verdict":"pass"' '"name":"Top.A.other","verdict":"pass"'

# Another statement of thm. A challenge declaration that differs fails every
# theorem.
solution main/statement <<'EOF'
Require Import Top.Defs.
Definition thm : forall A B : Prop, forall _ : A, forall _ : B, A := fun A B a _ => a.
Definition other : prop_id := fun A a => a.
EOF
verdict main/statement main.json '"name":"Top.A.thm","verdict":"fail"' \
  '"name":"Top.A.other","verdict":"fail","reason":"the challenge declaration Top.A.thm differs' \
  '{"name":"Top.A.thm","reason":'

# An axiom of the solution's own: permitted_axioms is empty by default.
solution main/axiom <<'EOF'
Require Import Top.Defs.
Axiom cheat : théorème_ÿ.
Definition thm : théorème_ÿ := cheat.
Definition other : prop_id := fun A a => a.
EOF
verdict main/axiom main.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the axiom Top.A.cheat is not permitted","axioms":["Top.A.cheat"]' \
  '"name":"Top.A.other","verdict":"pass"'

# The verdict is written whatever it says, and -axiom-free still sets the
# exit status.
rm -f "$out"
if compare main/axiom main.json -axiom-free; then fail "-axiom-free: exit 0"; fi
[ -f "$out" ] || fail "-axiom-free: no verdict file"
grep -qF 'Axioms or unsafe features found' "$log" || fail "-axiom-free: another error"

solution main/admitted <<'EOF'
Require Import Top.Defs.
Theorem thm : théorème_ÿ.
Proof. Admitted.
Definition other : prop_id := fun A a => a.
EOF
verdict main/admitted main.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the axiom Top.A.thm is not permitted"' \
  '"name":"Top.A.other","verdict":"pass"'

solution main/missing <<'EOF'
Require Import Top.Defs.
Definition other : prop_id := fun A a => a.
EOF
verdict main/missing main.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"missing"' \
  '"name":"Top.A.other","verdict":"fail","reason":"the challenge declaration Top.A.thm differs: missing"'

# The body of a definition of Defs.v is changed, and its type kept.
sed 's/^Definition prop_id := .*/Definition prop_id := forall A : Prop, forall _ : A, forall _ : A, A./' \
  "$d/main/ch/Defs.v" | compile main/body Defs.v
compile main/body A.v <<'EOF'
Require Import Top.Defs.
Definition thm : théorème_ÿ := fun A a _ => a.
Definition other : prop_id := thm.
EOF
verdict main/body main.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.Defs.prop_id differs' \
  '"name":"Top.A.other","verdict":"fail"' '{"name":"Top.Defs.prop_id","reason":'

# théorème_ÿ is given a body equal to the challenge's only once prop_id is
# unfolded, and the comparison does not reduce. The verdict escapes its name.
sed 's/^Definition théorème_ÿ := prop_id\./Definition théorème_ÿ := forall A : Prop, forall _ : A, A./' \
  "$d/main/ch/Defs.v" | compile main/name Defs.v
compile main/name A.v < "$d/main/honest/A.v"
verdict main/name main.json '"name":"Top.A.thm","verdict":"fail"' '"name":"Top.A.other","verdict":"fail"' \
  '{"name":"Top.Defs.th\u00e9or\u00e8me_\u00ff","reason":'

# The field P of the module type SIG is given a body. A module type is no
# constant of the environment, and is compared all the same. The reason
# names the field.
sed 's/^  Parameter P : Prop\./  Definition P := prop_id./' "$d/main/ch/Defs.v" |
  compile main/modtype Defs.v
compile main/modtype A.v < "$d/main/honest/A.v"
verdict main/modtype main.json '"name":"Top.A.thm","verdict":"fail"' \
  '{"name":"Top.Defs.SIG","reason":"the field P: the challenge leaves this declaration open and the solution defines it"}'

# An axiom that the proof reaches through a module whose signature hides it.
solution main/sealed <<'EOF'
Require Import Top.Defs.
Module Type HIDE.
  Parameter p : théorème_ÿ.
End HIDE.
Module Hidden : HIDE.
  Axiom cheat : théorème_ÿ.
  Definition p := cheat.
End Hidden.
Definition thm : théorème_ÿ := Hidden.p.
Definition other : prop_id := fun A a => a.
EOF
verdict main/sealed main.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the axiom Top.A.Hidden.cheat is not permitted"' \
  '"name":"Top.A.other","verdict":"pass"'

# A rewrite rule in a library that only the solution has, or in a module,
# fails every theorem unless the config sets rewrite_rules.
solution main/rlib < "$d/main/honest/A.v"
compile main/rlib R.v -allow-rewrite-rules <<'EOF'
Symbol s : Prop.
Rewrite Rule r := s => (forall A : Prop, forall _ : A, A).
EOF
verdict main/rlib main.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the solution declares a rewrite rule on Top.R.s"' \
  '"name":"Top.A.other","verdict":"fail","reason":"the solution declares a rewrite rule on Top.R.s"'
verdict main/rlib main-rules.json '"name":"Top.A.thm","verdict":"pass"' '"name":"Top.A.other","verdict":"pass"'
solution main/rmod -allow-rewrite-rules <<'EOF'
Require Import Top.Defs.
Module N.
  Symbol s : Prop.
  Rewrite Rule r := s => prop_id.
End N.
Definition thm : théorème_ÿ := fun A a => a.
Definition other : prop_id := thm.
EOF
verdict main/rmod main.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the solution declares a rewrite rule on Top.A.N.s"' \
  '"name":"Top.A.other","verdict":"fail"'

#### Declarations of the challenge that no theorem names: a solution may
#### give a body to one that the challenge leaves open only when it is a
#### proof, and may not change an inductive type.

compile open/ch A.v <<'EOF'
Unset Elimination Schemes.
Parameter P : Prop.
Lemma lem : forall A : Prop, forall _ : A, A.
Proof. Admitted.
Inductive t : Set := c : t.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config open > "$d/open.json"
# The type of lem is a proposition: the solution may prove it.
compile open/lem A.v <<'EOF'
Unset Elimination Schemes.
Parameter P : Prop.
Definition lem : forall A : Prop, forall _ : A, A := fun A a => a.
Inductive t : Set := c : t.
Definition thm : forall A : Prop, forall _ : A, A := lem.
EOF
verdict open/lem open.json '"name":"Top.A.thm","verdict":"pass"'
# The type of P, Prop, is a type and not a proposition: P is data, which the
# solution may not choose.
sed 's/^Parameter P : Prop\./Definition P : Prop := forall A : Prop, A./' "$d/open/lem/A.v" |
  compile open/data A.v
verdict open/data open.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.P differs: the challenge leaves this declaration open and the solution defines it"'
# t has one more constructor.
sed 's/^Inductive t : Set := c : t\./Inductive t : Set := c : t | d : t./' "$d/open/lem/A.v" |
  compile open/ctor A.v
verdict open/ctor open.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.t differs' \
  '{"name":"Top.A.t","reason":'
# A theorem the config names may be given a body whatever its sort: as a
# theorem, P may be defined.
cat > "$d/open-p.json" <<EOF
{"theorems": [{"name": "Top.A.thm"}, {"name": "Top.A.P"}],
 "challenge_files": [{"path": "A.vo", "sha256": "$(digest open/ch/A.vo)"}]}
EOF
verdict open/data open-p.json '"name":"Top.A.thm","verdict":"pass"' '"name":"Top.A.P","verdict":"pass"'

# A case <case> whose challenge, <case>/ch/A.v, leaves a constant L without
# a body and states thm about it, and whose solution <case>/defined proves L
# by Defined and thm from it. The config names both, so that the verdict of
# L shows whether its body is accepted. eq has an index, so a proof through
# it rests on indices not mattering, which the config tolerates on every
# object, as uip.json does. The run of <case>/defined holds each <text>;
# then <case>/qed, derived from it, proves L by Qed and leaves thm admitted:
# L passes, and thm fails on its own axiom.
open_lemma() { # <case> <text>...
  local c=$1
  shift
  cat > "$d/$c.json" <<EOF
{"theorems": [{"name": "Top.A.thm"}, {"name": "Top.A.L"}],
 "tolerated_flags": [{"kind": "indices-not-mattering"}],
 "challenge_files": [{"path": "A.vo", "sha256": "$(digest "$c/ch/A.vo")"}]}
EOF
  verdict "$c/defined" "$c.json" "$@"
  sed -e 's/ Defined\.$/ Qed./' -e 's/^Proof\. exact (eq_refl .*/Proof. Admitted./' \
    "$d/$c/defined/A.v" | compile "$c/qed" A.v
  verdict "$c/qed" "$c.json" \
    '"name":"Top.A.thm","verdict":"fail","reason":"the axiom Top.A.thm is not permitted"' \
    '"name":"Top.A.L","verdict":"pass"' '"declarations":[]'
}

# The statement of thm names the proof L, which the challenge leaves without
# a body: L does not unfold there, and thm is not provable. The challenge
# states the type of L in Prop. A solution that proves L by Defined proves
# thm by conversion, which changes what thm states, so L must be opaque. The
# reason names thm, the declaration that names L.
compile named/ch A.v <<'EOF'
Unset Elimination Schemes.
Inductive nat : Set := O : nat | S : forall _ : nat, nat.
Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.
Inductive ex (A : Type) (P : forall _ : A, Prop) : Prop :=
  ex_intro : forall x : A, forall _ : P x, ex A P.
Lemma L : ex nat (fun n => eq nat n O).
Proof. Admitted.
Theorem thm : eq (ex nat (fun n => eq nat n O)) L (ex_intro nat (fun n => eq nat n O) O (eq_refl nat O)).
Proof. Admitted.
EOF
compile named/defined A.v <<'EOF'
Require Import Corelib.Init.Ltac.
Unset Elimination Schemes.
Inductive nat : Set := O : nat | S : forall _ : nat, nat.
Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.
Inductive ex (A : Type) (P : forall _ : A, Prop) : Prop :=
  ex_intro : forall x : A, forall _ : P x, ex A P.
Lemma L : ex nat (fun n => eq nat n O).
Proof. exact (ex_intro nat (fun n => eq nat n O) O (eq_refl nat O)). Defined.
Theorem thm : eq (ex nat (fun n => eq nat n O)) L (ex_intro nat (fun n => eq nat n O) O (eq_refl nat O)).
Proof. exact (eq_refl (ex nat (fun n => eq nat n O)) L). Qed.
EOF
open_lemma named \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.L differs: the challenge leaves this constant without a body, the challenge declaration Top.A.thm names it, and the solution gives it a transparent body"' \
  '"name":"Top.A.L","verdict":"fail","reason":"the challenge leaves this constant without a body'

# The same with L sort-polymorphic: the challenge states the type of L in
# the sort variable s, and thm names L at the instance Prop, where L is a
# proof. The run cannot tell s from Prop, so L must be opaque: a transparent
# L proves thm by conversion as in named.
compile poly/ch A.v <<'EOF'
Unset Elimination Schemes.
Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.
Set Universe Polymorphism.
Inductive sbool@{s;|} : Univ@{s;Set} := strue | sfalse.
Lemma L@{s;|} : sbool@{s;}.
Proof. Admitted.
Unset Universe Polymorphism.
Theorem thm : eq sbool@{Prop;} L@{Prop;} strue@{Prop;}.
Proof. Admitted.
EOF
compile poly/defined A.v <<'EOF'
Require Import Corelib.Init.Ltac.
Unset Elimination Schemes.
Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.
Set Universe Polymorphism.
Inductive sbool@{s;|} : Univ@{s;Set} := strue | sfalse.
Lemma L@{s;|} : sbool@{s;}.
Proof. exact strue@{s;}. Defined.
Unset Universe Polymorphism.
Theorem thm : eq sbool@{Prop;} L@{Prop;} strue@{Prop;}.
Proof. exact (eq_refl sbool@{Prop;} L@{Prop;}). Qed.
EOF
open_lemma poly \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.L differs: the challenge leaves this constant without a body, the challenge declaration Top.A.thm names it, and the solution gives it a transparent body"' \
  '"name":"Top.A.L","verdict":"fail","reason":"the challenge leaves this constant without a body'

# The same with the type of L in a global sort: B lives in the sort s that a
# Sort command declares, and L is an element of B. The run cannot tell
# whether s is meant for propositions, so L must be opaque: a transparent L
# proves thm by conversion as in named. eq is stated over B.
compile gsort/ch A.v <<'EOF'
Unset Elimination Schemes.
Sort s.
Inductive B : Univ@{s;Set} := b : B.
Inductive eq (x : B) : forall _ : B, Prop := eq_refl : eq x x.
Lemma L : B.
Proof. Admitted.
Theorem thm : eq L b.
Proof. Admitted.
EOF
compile gsort/defined A.v <<'EOF'
Require Import Corelib.Init.Ltac.
Unset Elimination Schemes.
Sort s.
Inductive B : Univ@{s;Set} := b : B.
Inductive eq (x : B) : forall _ : B, Prop := eq_refl : eq x x.
Lemma L : B.
Proof. exact b. Defined.
Theorem thm : eq L b.
Proof. exact (eq_refl L). Qed.
EOF
open_lemma gsort \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.L differs: the challenge leaves this constant without a body, the challenge declaration Top.A.thm names it, and the solution gives it a transparent body"' \
  '"name":"Top.A.L","verdict":"fail","reason":"the challenge leaves this constant without a body'

# The same with the type of L written through Spec, a definition typed Type
# that unfolds to a proposition. The challenge states the type of L in Type,
# so L is data: since the config names it, the solution may define it
# transparently, and thm then holds by conversion. A challenge that wants L
# kept opaque states its type in Prop, as named does. Spec is typed
# Type@{u}, a named level, so that its type stays in Type whatever universe
# minimization does.
compile alias/ch A.v <<'EOF'
Unset Elimination Schemes.
Inductive nat : Set := O : nat | S : forall _ : nat, nat.
Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.
Inductive ex (A : Type) (P : forall _ : A, Prop) : Prop :=
  ex_intro : forall x : A, forall _ : P x, ex A P.
Universe u.
Definition Spec : Type@{u} := ex nat (fun n => eq nat n O).
Lemma L : Spec.
Proof. Admitted.
Theorem thm : eq Spec L (ex_intro nat (fun n => eq nat n O) O (eq_refl nat O)).
Proof. Admitted.
EOF
compile alias/defined A.v <<'EOF'
Require Import Corelib.Init.Ltac.
Unset Elimination Schemes.
Inductive nat : Set := O : nat | S : forall _ : nat, nat.
Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.
Inductive ex (A : Type) (P : forall _ : A, Prop) : Prop :=
  ex_intro : forall x : A, forall _ : P x, ex A P.
Universe u.
Definition Spec : Type@{u} := ex nat (fun n => eq nat n O).
Lemma L : Spec.
Proof. exact (ex_intro nat (fun n => eq nat n O) O (eq_refl nat O)). Defined.
Theorem thm : eq Spec L (ex_intro nat (fun n => eq nat n O) O (eq_refl nat O)).
Proof. exact (eq_refl Spec L). Qed.
EOF
open_lemma alias '"name":"Top.A.thm","verdict":"pass"' '"name":"Top.A.L","verdict":"pass"' \
  '"declarations":[]'

# The same with the type of L a match stuck on a variable: T b is a match on
# b, a proposition when b is true and nat when it is false, and L true is a
# proof. The challenge states the type of L in Set or Type, not in Prop, so
# L is data: since the config names it, the solution may define it
# transparently, and thm then holds by conversion.
compile stuck/ch A.v <<'EOF'
Unset Elimination Schemes.
Inductive bool : Set := true : bool | false : bool.
Inductive nat : Set := O : nat | S : forall _ : nat, nat.
Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.
Inductive ex (A : Type) (P : forall _ : A, Prop) : Prop :=
  ex_intro : forall x : A, forall _ : P x, ex A P.
Definition T (b : bool) : Type :=
  match b with true => ex nat (fun n => eq nat n O) | false => nat end.
Lemma L : forall b : bool, T b.
Proof. Admitted.
Theorem thm : eq (T true) (L true) (ex_intro nat (fun n => eq nat n O) O (eq_refl nat O)).
Proof. Admitted.
EOF
compile stuck/defined A.v <<'EOF'
Require Import Corelib.Init.Ltac.
Unset Elimination Schemes.
Inductive bool : Set := true : bool | false : bool.
Inductive nat : Set := O : nat | S : forall _ : nat, nat.
Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.
Inductive ex (A : Type) (P : forall _ : A, Prop) : Prop :=
  ex_intro : forall x : A, forall _ : P x, ex A P.
Definition T (b : bool) : Type :=
  match b with true => ex nat (fun n => eq nat n O) | false => nat end.
Lemma L : forall b : bool, T b.
Proof. exact (fun b => match b return T b with true => ex_intro nat (fun n => eq nat n O) O (eq_refl nat O) | false => O end). Defined.
Theorem thm : eq (T true) (L true) (ex_intro nat (fun n => eq nat n O) O (eq_refl nat O)).
Proof. exact (eq_refl (T true) (L true)). Qed.
EOF
open_lemma stuck '"name":"Top.A.thm","verdict":"pass"' '"name":"Top.A.L","verdict":"pass"' \
  '"declarations":[]'

# The same with the type of L a variable the products bind: L takes a type A
# and an element of A, and returns an element of A, so L nat O is O once L
# is the identity, and thm holds by conversion. A may be a proposition, and
# L A a proof of it, but the challenge states the type of L in Type, so L is
# data: since the config names it, the solution may define it transparently.
# u is a named level, as in alias, so that both sides keep it whatever
# universe minimization does.
compile rel/ch A.v <<'EOF'
Unset Elimination Schemes.
Inductive nat : Set := O : nat | S : forall _ : nat, nat.
Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.
Universe u.
Lemma L : forall A : Type@{u}, forall _ : A, A.
Proof. Admitted.
Theorem thm : eq nat (L nat O) O.
Proof. Admitted.
EOF
compile rel/defined A.v <<'EOF'
Require Import Corelib.Init.Ltac.
Unset Elimination Schemes.
Inductive nat : Set := O : nat | S : forall _ : nat, nat.
Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.
Universe u.
Lemma L : forall A : Type@{u}, forall _ : A, A.
Proof. exact (fun A a => a). Defined.
Theorem thm : eq nat (L nat O) O.
Proof. exact (eq_refl nat O). Qed.
EOF
open_lemma rel '"name":"Top.A.thm","verdict":"pass"' '"name":"Top.A.L","verdict":"pass"' \
  '"declarations":[]'

# A function f that the challenge leaves open and a lemma f_spec about it,
# both named by the config: the challenge asks the solution to choose f, and
# f_spec is provable only if f unfolds, so f may be transparent though
# f_spec names it. The challenge states the type of f in Set, so f is data,
# which may be transparent when another declaration names it. eq has an
# index, which the config tolerates as named.json does.
compile spec/ch A.v <<'EOF'
Unset Elimination Schemes.
Inductive nat : Set := O : nat | S : forall _ : nat, nat.
Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.
Definition f : forall _ : nat, nat.
Proof. Admitted.
Theorem f_spec : forall n : nat, eq nat (f n) (S n).
Proof. Admitted.
EOF
cat > "$d/spec.json" <<EOF
{"theorems": [{"name": "Top.A.f"}, {"name": "Top.A.f_spec"}],
 "tolerated_flags": [{"kind": "indices-not-mattering"}],
 "challenge_files": [{"path": "A.vo", "sha256": "$(digest spec/ch/A.vo)"}]}
EOF
compile spec/defined A.v <<'EOF'
Unset Elimination Schemes.
Inductive nat : Set := O : nat | S : forall _ : nat, nat.
Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.
Definition f : forall _ : nat, nat := fun n => S n.
Definition f_spec : forall n : nat, eq nat (f n) (S n) := fun n => eq_refl nat (S n).
EOF
verdict spec/defined spec.json '"name":"Top.A.f","verdict":"pass"' \
  '"name":"Top.A.f_spec","verdict":"pass"' '"declarations":[]'

# The same over a primitive type, declared alike on both sides: the
# challenge states the type of f, int -> int, in Set, so f is data and may be
# transparent. int is a constant without a body that the proofs reach, so
# the config permits it as an axiom.
compile prim/ch A.v <<'EOF'
Unset Elimination Schemes.
Primitive int := #int63_type.
Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.
Definition f : forall _ : int, int.
Proof. Admitted.
Theorem f_spec : forall x : int, eq int (f x) x.
Proof. Admitted.
EOF
cat > "$d/prim.json" <<EOF
{"theorems": [{"name": "Top.A.f"}, {"name": "Top.A.f_spec"}],
 "permitted_axioms": ["Top.A.int"],
 "tolerated_flags": [{"kind": "indices-not-mattering"}],
 "challenge_files": [{"path": "A.vo", "sha256": "$(digest prim/ch/A.vo)"}]}
EOF
compile prim/defined A.v <<'EOF'
Unset Elimination Schemes.
Primitive int := #int63_type.
Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.
Definition f : forall _ : int, int := fun x => x.
Definition f_spec : forall x : int, eq int (f x) x := fun x => eq_refl int x.
EOF
verdict prim/defined prim.json '"name":"Top.A.f","verdict":"pass"' \
  '"name":"Top.A.f_spec","verdict":"pass"' '"declarations":[]'

# A parameter T that the solution declares as a primitive type, of the same
# type Set: both are constants without a body, but the literals of a
# primitive type have it for type, so the solution proves T inhabited, which
# the challenge's T is not known to be. Its proof of thm holds a literal of
# T, which Eval compute gives for max_length (the primitive constant
# #array_max_length, a definition whose body is that literal), so it reaches
# no constant but T. The config permits T as an axiom, so that only the
# comparison of primitive types refuses it.
compile primtype/ch A.v <<'EOF'
Unset Elimination Schemes.
Inductive True : Prop := I : True.
Inductive ex (A : Type) (P : forall _ : A, Prop) : Prop :=
  ex_intro : forall x : A, forall _ : P x, ex A P.
Parameter T : Set.
Theorem thm : ex T (fun _ => True).
Proof. Admitted.
EOF
config primtype '"permitted_axioms": ["Top.A.T"],' > "$d/primtype.json"
compile primtype/literal A.v <<'EOF'
Unset Elimination Schemes.
Inductive True : Prop := I : True.
Inductive ex (A : Type) (P : forall _ : A, Prop) : Prop :=
  ex_intro : forall x : A, forall _ : P x, ex A P.
Primitive T := #int63_type.
Primitive max_length := #array_max_length.
Definition thm : ex T (fun _ => True) :=
  Eval compute in ex_intro T (fun _ => True) max_length I.
EOF
verdict primtype/literal primtype.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.T differs: this constant is no primitive type in the challenge and the primitive type #int63_type in the solution"' \
  '{"name":"Top.A.T","reason":"this constant is no primitive type in the challenge and the primitive type #int63_type in the solution"}'

# The other way round: the challenge declares T as a primitive type, and
# the solution as a parameter of the same type Set. The solution's T has no
# literals, so it is not the challenge's T either. The config permits T as
# an axiom, as primtype.json does.
compile primrev/ch A.v <<'EOF'
Unset Elimination Schemes.
Inductive True : Prop := I : True.
Primitive T := #int63_type.
Theorem thm : forall _ : T, True.
Proof. Admitted.
EOF
config primrev '"permitted_axioms": ["Top.A.T"],' > "$d/primrev.json"
compile primrev/parameter A.v <<'EOF'
Unset Elimination Schemes.
Inductive True : Prop := I : True.
Parameter T : Set.
Definition thm : forall _ : T, True := fun _ => I.
EOF
verdict primrev/parameter primrev.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.T differs: this constant is the primitive type #int63_type in the challenge and no primitive type in the solution"' \
  '{"name":"Top.A.T","reason":"this constant is the primitive type #int63_type in the challenge and no primitive type in the solution"}'

# A primitive type registered inside a module M that the signature S seals.
# S declares T as a parameter, and so does the challenge's M, sealed by the
# same S: through S, both sides declare M.T alike. The kernel keeps the
# registration once M is closed, whatever S declares, so the literals of
# #int63_type have the type M.T in the solution, and only the comparison of
# primitive types tells the two M.T apart. The config permits M.T as an
# axiom, as primtype.json does T.
compile primmod/ch A.v <<'EOF'
Unset Elimination Schemes.
Inductive True : Prop := I : True.
Module Type S.
  Parameter T : Set.
End S.
Module M : S.
  Parameter T : Set.
End M.
Theorem thm : forall _ : M.T, True.
Proof. Admitted.
EOF
config primmod '"permitted_axioms": ["Top.A.M.T"],' > "$d/primmod.json"
compile primmod/sealed A.v <<'EOF'
Unset Elimination Schemes.
Inductive True : Prop := I : True.
Module Type S.
  Parameter T : Set.
End S.
Module M : S.
  Primitive T := #int63_type.
End M.
Definition thm : forall _ : M.T, True := fun _ => I.
EOF
verdict primmod/sealed primmod.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.M.T differs: this constant is no primitive type in the challenge and the primitive type #int63_type in the solution"' \
  '{"name":"Top.A.M.T","reason":"this constant is no primitive type in the challenge and the primitive type #int63_type in the solution"}'

# A functor module type. A functor parameter is named by a counter of the
# process that compiled it, so a solution that declares one more functor
# before FT numbers the parameters of FT otherwise: the comparison renames
# them, by position.
compile functor/ch A.v <<'EOF'
Module Type SIG.
  Parameter P : Prop.
End SIG.
Module Type FT (X : SIG) (Y : SIG).
  Parameter q : X.P.
End FT.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config functor > "$d/functor.json"
compile functor/honest A.v <<'EOF'
Module Type SIG.
  Parameter P : Prop.
End SIG.
Module Type G (Z : SIG).
End G.
Module Type FT (X : SIG) (Y : SIG).
  Parameter q : X.P.
End FT.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict functor/honest functor.json '"name":"Top.A.thm","verdict":"pass"' '"declarations":[]'
sed 's/^  Parameter q : X\.P\./  Parameter q : Y.P./' "$d/functor/honest/A.v" |
  compile functor/swapped A.v
verdict functor/swapped functor.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.FT differs'

# The name of a functor parameter is that counter, its identifier and its
# library, so a parameter of one side may have the name of a parameter of
# the other. Each challenge parameter is renamed once, and a name the
# renaming gives is not renamed again. Here the solution declares G first,
# so the outer parameter Y of its FT has the name of the inner parameter Y
# of the challenge's FT; renamed twice, X would stand for W.
compile functor/clash A.v <<'EOF'
Module Type SIG.
  Parameter P : Prop.
End SIG.
Module Type G (Z : SIG).
End G.
Module Type FT (Y : SIG) (W : SIG).
  Parameter q : Y.P.
End FT.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict functor/clash functor.json '"name":"Top.A.thm","verdict":"pass"' '"declarations":[]'
sed 's/^  Parameter q : Y\.P\./  Parameter q : W.P./' "$d/functor/clash/A.v" |
  compile functor/clash-swapped A.v
verdict functor/clash-swapped functor.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.FT differs'
# The other way round: the challenge declares G first, so the inner
# parameter X of the solution's FT has the name of the outer parameter X of
# the challenge's FT; renamed twice, Y would stand for V.
compile functorg/ch A.v <<'EOF'
Module Type SIG.
  Parameter P : Prop.
End SIG.
Module Type G (Z : SIG).
End G.
Module Type FT (X : SIG) (Y : SIG).
  Parameter q : Y.P.
End FT.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config functorg > "$d/functorg.json"
compile functorg/clash A.v <<'EOF'
Module Type SIG.
  Parameter P : Prop.
End SIG.
Module Type FT (V : SIG) (X : SIG).
  Parameter q : X.P.
End FT.
Module Type G (Z : SIG).
End G.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict functorg/clash functorg.json '"name":"Top.A.thm","verdict":"pass"' '"declarations":[]'
sed 's/^  Parameter q : X\.P\./  Parameter q : V.P./' "$d/functorg/clash/A.v" |
  compile functorg/clash-swapped A.v
verdict functorg/clash-swapped functorg.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.FT differs'

# A functor parameter whose type differs: the solution's FT takes X : SIG2,
# whose P is defined, where the challenge's takes X : SIG. The reason names
# the functor parameter by its identifier, and the field of its type that
# differs.
compile paramtype/ch A.v <<'EOF'
Module Type SIG.
  Parameter P : Prop.
End SIG.
Module Type SIG2.
  Definition P : Prop := forall A : Prop, A.
End SIG2.
Module Type FT (X : SIG).
  Parameter q : X.P.
End FT.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config paramtype > "$d/paramtype.json"
compile paramtype/other A.v <<'EOF'
Module Type SIG.
  Parameter P : Prop.
End SIG.
Module Type SIG2.
  Definition P : Prop := forall A : Prop, A.
End SIG2.
Module Type FT (X : SIG2).
  Parameter q : X.P.
End FT.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict paramtype/other paramtype.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.FT differs: the functor parameter X: the field P: the challenge leaves this declaration open and the solution defines it"' \
  '{"name":"Top.A.FT","reason":"the functor parameter X: the field P: the challenge leaves this declaration open and the solution defines it"}'

# A field of a module type whose type names another field. No environment
# holds the fields of a module type, so the comparison does not type the
# field x, and x, which the challenge leaves without a body, may not be
# given one: the run writes a verdict that says so, and names the field.
compile field/ch A.v <<'EOF'
Module Type T.
  Parameter t : Set.
  Parameter y : t.
  Parameter x : t.
End T.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config field > "$d/field.json"
compile field/defined A.v <<'EOF'
Module Type T.
  Parameter t : Set.
  Parameter y : t.
  Definition x : t := y.
End T.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict field/defined field.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.T differs: the field x: the challenge leaves this declaration open and the solution defines it"' \
  '{"name":"Top.A.T","reason":"the field x: the challenge leaves this declaration open and the solution defines it"}'

# The same with a field whose type, True, is a proposition, which typed in
# the environment would let the solution prove it. The comparison does not
# type a field, so x may not be given a body either.
compile fieldprop/ch A.v <<'EOF'
Unset Elimination Schemes.
Inductive True : Prop := I : True.
Module Type T.
  Parameter x : True.
End T.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config fieldprop > "$d/fieldprop.json"
compile fieldprop/defined A.v <<'EOF'
Unset Elimination Schemes.
Inductive True : Prop := I : True.
Module Type T.
  Definition x : True := I.
End T.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict fieldprop/defined fieldprop.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.T differs: the field x: the challenge leaves this declaration open and the solution defines it"' \
  '{"name":"Top.A.T","reason":"the field x: the challenge leaves this declaration open and the solution defines it"}'

# A template-polymorphic inductive type. An application of Box is typed by
# its template data, which says which parameters bind a universe.
compile template/ch A.v <<'EOF'
Unset Elimination Schemes.
#[universes(template)]
Inductive Box@{i j} (A : Type@{i}) (B : Type@{j}) : Type@{max(i,j)} :=
  box : forall _ : A, forall _ : B, Box A B.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config template > "$d/template.json"
compile template/honest A.v <<'EOF'
Unset Elimination Schemes.
#[universes(template)]
Inductive Box@{i j} (A : Type@{i}) (B : Type@{j}) : Type@{max(i,j)} :=
  box : forall _ : A, forall _ : B, Box A B.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict template/honest template.json '"name":"Top.A.thm","verdict":"pass"' '"declarations":[]'
# The level of B is the global level u: B binds nothing. The parameters of
# Box differ too, B : Type@{u} against the challenge's B over the second
# level its template context binds, but which parameters bind a level is
# compared first.
compile template/global A.v <<'EOF'
Unset Elimination Schemes.
Universe u.
#[universes(template)]
Inductive Box@{i} (A : Type@{i}) (B : Type@{u}) : Type@{max(i,u)} :=
  box : forall _ : A, forall _ : B, Box A B.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict template/global template.json '"name":"Top.A.thm","verdict":"fail"' \
  '{"name":"Top.A.Box","reason":"the template-polymorphic parameters"}'

# The template context of Box constrains the level that it binds below u,
# which U names, so an application of Box takes a type of a level below u.
# helper declares a level before the challenge's: the two sides number the
# levels differently. A copy whose Box binds a level below w, which W names,
# differs in its template context alone: the other fields of Box are the
# challenge's.
compile templatec/ch A.v <<'EOF'
Unset Elimination Schemes.
Universe u w.
Definition U := Type@{u}.
Definition W := Type@{w}.
#[universes(template)]
Inductive Box@{i | i <= u} (A : Type@{i}) : Type@{i} := box : forall _ : A, Box A.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config templatec > "$d/templatec.json"
compile templatec/honest A.v <<'EOF'
Definition helper := Type.
Unset Elimination Schemes.
Universe u w.
Definition U := Type@{u}.
Definition W := Type@{w}.
#[universes(template)]
Inductive Box@{i | i <= u} (A : Type@{i}) : Type@{i} := box : forall _ : A, Box A.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict templatec/honest templatec.json '"name":"Top.A.thm","verdict":"pass"' '"declarations":[]'
sed 's/^Inductive Box@{i | i <= u}/Inductive Box@{i | i <= w}/' "$d/templatec/honest/A.v" |
  compile templatec/other A.v
verdict templatec/other templatec.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.Box differs: the universe context has other constraints"' \
  '{"name":"Top.A.Box","reason":"the universe context has other constraints"}'

#### Runs that rocqchk refuses.

# Errors in the config, found as it is read: "0" stands for a digest.
bad_config() { # <error text> <config>
  printf '%s\n' "$2" > "$d/bad.json"
  refused "$1" compare main/honest bad.json
}
bad_config 'the key proofs of the config is not a key this version knows' \
  '{"theorems": [{"name": "Top.A.thm"}], "proofs": [], "challenge_files": [{"path": "A.vo", "sha256": "0"}]}'
bad_config 'the key theorems appears twice' \
  '{"theorems": [{"name": "Top.A.thm"}], "theorems": [], "challenge_files": [{"path": "A.vo", "sha256": "0"}]}'
bad_config 'there are bytes after the top-level value' \
  '{"theorems": [{"name": "Top.A.thm"}], "challenge_files": [{"path": "A.vo", "sha256": "0"}]} {}'
bad_config 'the config names no theorem' \
  '{"theorems": [], "challenge_files": [{"path": "A.vo", "sha256": "0"}]}'
bad_config 'the config has no challenge_files' \
  '{"theorems": [{"name": "Top.A.thm"}]}'
bad_config 'the tolerated flag type-in-type is refused with an object or without' \
  '{"theorems": [{"name": "Top.A.thm"}], "tolerated_flags": [{"kind": "type-in-type", "object": "Top.A.thm"}],
    "challenge_files": [{"path": "A.vo", "sha256": "0"}]}'
bad_config 'the tolerated flag unchecked-eliminations needs an object' \
  '{"theorems": [{"name": "Top.A.thm"}], "tolerated_flags": [{"kind": "unchecked-eliminations"}],
    "challenge_files": [{"path": "A.vo", "sha256": "0"}]}'
bad_config 'the tolerated flag answer-universe-constraints does not name an object' \
  '{"theorems": [{"name": "Top.A.thm"}], "tolerated_flags": [{"kind": "answer-universe-constraints", "object": "Top.A.thm"}],
    "challenge_files": [{"path": "A.vo", "sha256": "0"}]}'

# A challenge file that is missing, or whose digest is not the config's.
bad_config 'B.vo is not there' \
  '{"theorems": [{"name": "Top.A.thm"}], "challenge_files": [{"path": "B.vo", "sha256": "0"}]}'
bad_config 'A.vo has sha256' \
  '{"theorems": [{"name": "Top.A.thm"}], "challenge_files": [{"path": "A.vo", "sha256": "0"}]}'

# A theorem that the challenge does not declare.
sed 's/Top\.A\.other/Top.A.none/' "$d/main.json" > "$d/bad.json"
refused 'The config names the theorem Top.A.none, which the challenge does not hold' \
  compare main/honest bad.json

# -compare, -challenge and -compare-out go together, and not with -package.
refused 'go together' chk -Q "$d/main/honest" Top -compare "$d/main.json" -compare-out "$out" Top.A
refused 'go together' chk -Q "$d/main/honest" Top -challenge "$d/main/ch" -compare-out "$out" Top.A
refused 'Option -package cannot be used with -compare' chk -package p -Q "$d/main/honest" Top \
  -compare "$d/main.json" -challenge "$d/main/ch" -compare-out "$out" Top.A
# Without -compare-out, no verdict file is named.
if chk -Q "$d/main/honest" Top -compare "$d/main.json" -challenge "$d/main/ch" Top.A; then
  fail "a run without -compare-out: exit 0"
fi
grep -qF 'go together' "$log" || fail "a run without -compare-out: another error"

# A -Q of the empty root, or of a top-level name of the default load path.
mkdir "$d/empty"
refused 'is bound to the empty root' compare main/honest main.json -Q "$d/empty" ""
refused 'is bound to Corelib, a name the default load path serves' \
  compare main/honest main.json -Q "$d/empty" Corelib

# A library outside the challenge's root and not pre-checked: from another
# bound root, or from the working directory.
mkdir "$d/lib" "$d/cwd"
echo 'Definition v := Prop.' > "$d/lib/V.v"
$coqc -noinit -native-compiler no -Q "$d/lib" Vendor "$d/lib/V.v"
{ echo 'Require Vendor.V.'; cat "$d/main/honest/A.v"; } | solution main/vendor -Q "$d/lib" Vendor
refused 'which the challenge does not stand in for and the config does not declare pre-checked' \
  compare main/vendor main.json -Q "$d/lib" Vendor
# The solution's build finds W through ROCQPATH, and rocqchk in the working
# directory.
echo 'Definition w := Prop.' > "$d/cwd/W.v"
ROCQPATH=$d/cwd $coqc -noinit -native-compiler no "$d/cwd/W.v"
{ echo 'Require W.'; cat "$d/main/honest/A.v"; } | ROCQPATH=$d/cwd solution main/cwd
refused 'in the working directory' in_dir "$d/cwd" compare main/cwd main.json
# The load path finds X in an XDG directory, which it searches before the
# installation's directories, and the solution's build finds it there too.
# No trusted directory holds it: the corelib directory, user-contrib and
# those of ROCQPATH.
mkdir -p "$d/xdg/coq"
echo 'Definition x := Prop.' > "$d/xdg/coq/X.v"
XDG_DATA_HOME=$d/xdg $coqc -noinit -native-compiler no "$d/xdg/coq/X.v"
{ echo 'Require X.'; cat "$d/main/honest/A.v"; } | XDG_DATA_HOME=$d/xdg solution main/xdg
XDG_DATA_HOME=$d/xdg refused 'which is under none of the directories a -compare run trusts' \
  compare main/xdg main.json
# The same with HOME and XDG_DATA_HOME unset: the load path then takes
# ./.local/share/coq, below the working directory, for the XDG directory.
mkdir -p "$d/nohome/.local/share/coq"
echo 'Definition y := Prop.' > "$d/nohome/.local/share/coq/Y.v"
XDG_DATA_HOME=$d/nohome/.local/share $coqc -noinit -native-compiler no "$d/nohome/.local/share/coq/Y.v"
{ echo 'Require Y.'; cat "$d/main/honest/A.v"; } | XDG_DATA_HOME=$d/nohome/.local/share solution main/nohome
no_home() { (unset HOME XDG_DATA_HOME HOMEDRIVE HOMEPATH USERPROFILE; cd "$d/nohome" && "$@"); }
refused 'which is under none of the directories a -compare run trusts' no_home compare main/nohome main.json

# The libraries named for checking lie under two roots, Top and Vendor, and
# the challenge directory stands in for one root only. Two -Q of one root
# are one root.
refused 'lie under more than one root that -Q or -R binds: Top, Vendor' \
  chk -Q "$d/main/honest" Top -Q "$d/lib" Vendor -compare "$d/main.json" \
  -challenge "$d/main/ch" -compare-out "$out" Top.A Vendor.V
ran 'two -Q of Top' compare main/honest main.json -Q "$d/empty" Top
holds 'two -Q of Top' '"name":"Top.A.thm","verdict":"pass"' '"name":"Top.A.other","verdict":"pass"'
# The library named for checking lies under no root: the load path finds W
# in the working directory, and no -Q binds a root.
refused 'lie under no root that -Q or -R binds' \
  in_dir "$d/cwd" chk -compare "$d/main.json" -challenge "$d/main/ch" -compare-out "$out" W

# The challenge directory lacks Defs.vo, which A.vo depends on, and the load
# path finds the solution's behind it: a copy of the challenge's, which would
# then be compared with itself. A challenge library comes from the challenge
# directory.
mkdir -p "$d/nodefs/ch" "$d/nodefs/sol"
cp "$d/main/ch/A.vo" "$d/nodefs/ch/"
cp "$d/main/ch/Defs.vo" "$d/nodefs/sol/"
compile nodefs/sol A.v < "$d/main/honest/A.v"
config nodefs > "$d/nodefs.json"
refused 'which is not under the challenge directory' compare nodefs/sol nodefs.json

#### A shared library, Lib.X: a stand-in for an installed library, which
#### ROCQPATH reaches and no -Q binds. Both sides read it from one file.

mkdir -p "$d/rp/Lib" "$d/rp2/Lib"
echo 'Definition l := Prop.' > "$d/rp/Lib/X.v"
ROCQPATH=$d/rp $coqc -noinit -native-compiler no "$d/rp/Lib/X.v"
cp "$d/rp/Lib/X.vo" "$d/rp2/Lib/"
ROCQPATH=$d/rp compile shared/ch A.v <<'EOF'
Require Lib.X.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config shared > "$d/shared.json"
ROCQPATH=$d/rp compile shared/sol A.v <<'EOF'
Require Lib.X.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
# ROCQPATH lists rp2 too, behind rp, with a copy of X.vo.
ROCQPATH=$d/rp:$d/rp2 verdict shared/sol shared.json '"name":"Top.A.thm","verdict":"pass"'
# A link in the challenge directory to rp's Lib: the challenge load binds it
# to Top.Lib, so that on the challenge side the name Lib.X resolves to rp2's
# copy, the same bytes in another file.
ln -s "$d/rp/Lib" "$d/shared/ch/Lib"
ROCQPATH=$d/rp:$d/rp2 refused 'The challenge loaded the shared library Lib.X from' \
  compare shared/sol shared.json
# Lib.X pre-checked: the config pins its sha256, and the challenge load,
# which the link makes find the name in rp2 or rp3, must read pinned bytes.
# rp2's copy has them. rp3's X.vo has one byte more at its end, which the
# loader never reads: the digest that each library naming Lib.X records
# still matches it, as a forged file's would, and only its sha256 refuses
# it.
mkdir -p "$d/rp3/Lib"
cp "$d/rp/Lib/X.vo" "$d/rp3/Lib/"
printf 'x' >> "$d/rp3/Lib/X.vo"
config shared "\"prechecked\": [{\"library\": \"Lib.X\", \"sha256\": \"$(digest rp/Lib/X.vo)\"}]," \
  > "$d/shared-pre.json"
ROCQPATH=$d/rp:$d/rp2 verdict shared/sol shared-pre.json '"name":"Top.A.thm","verdict":"pass"'
ROCQPATH=$d/rp:$d/rp3 refused 'The challenge loaded the pre-checked library Lib.X from' \
  compare shared/sol shared-pre.json

#### The trusted directories: a shared library from user-contrib, here of a
#### -coqlib that stands in for an installation, and one from COQPATH.

# The -coqlib directory holds the corelib of the installation in use (the
# one ROCQLIB selects), linked by its absolute path, and an empty plugins
# directory, which an installation must have.
rocqlib=$(cd "$("$BIN"rocqchk -where)" && pwd)
mkdir -p "$d/coqlib/plugins" "$d/coqlib/user-contrib/Uc" "$d/cp/Cp"
ln -s "$rocqlib/theories" "$d/coqlib/theories"
echo 'Definition u := Prop.' > "$d/coqlib/user-contrib/Uc/U.v"
$coqc -noinit -native-compiler no -Q "$d/coqlib/user-contrib/Uc" Uc "$d/coqlib/user-contrib/Uc/U.v"
{ echo 'Require Uc.U.'; cat "$d/main/honest/A.v"; } | solution main/uc -Q "$d/coqlib/user-contrib/Uc" Uc
ran 'main/uc with -coqlib' compare main/uc main.json -coqlib "$d/coqlib"
holds 'main/uc with -coqlib' '"name":"Top.A.thm","verdict":"pass"' '"name":"Top.A.other","verdict":"pass"'
echo 'Definition c := Prop.' > "$d/cp/Cp/C.v"
$coqc -noinit -native-compiler no -Q "$d/cp/Cp" Cp "$d/cp/Cp/C.v"
{ echo 'Require Cp.C.'; cat "$d/main/honest/A.v"; } | solution main/cp -Q "$d/cp/Cp" Cp
COQPATH=$d/cp ran 'main/cp with COQPATH' compare main/cp main.json
holds 'main/cp with COQPATH' '"name":"Top.A.thm","verdict":"pass"' '"name":"Top.A.other","verdict":"pass"'

#### -norec checks the libraries it names, and loads the libraries they
#### depend on without a check.

compile norec/ch A.v <<'EOF'
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config norec > "$d/norec.json"
compile norec/sol Helper.v <<'EOF'
Definition h : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
compile norec/sol A.v <<'EOF'
Require Top.Helper.
Definition thm : forall A : Prop, forall _ : A, A := Top.Helper.h.
EOF
# Top.A and Top.Helper are both checked.
verdict norec/sol norec.json '"name":"Top.A.thm","verdict":"pass"'
# Only Top.A is checked, and the challenge has no counterpart for
# Top.Helper: nothing would look at it. Refused, unless -admit names it.
norec() { # <config> [rocqchk options]
  local config=$d/$1
  shift
  chk -Q "$d/norec/sol" Top "$@" -compare "$config" -challenge "$d/norec/ch" \
    -compare-out "$out" -norec Top.A
}
refused 'The solution library Top.Helper was loaded without a check' norec norec.json
ran '-admit Top.Helper -norec Top.A' norec norec.json -admit Top.Helper
holds '-admit Top.Helper -norec Top.A' '"name":"Top.A.thm","verdict":"pass"' \
  '"admitted":["Top.Helper"]}'

# Or unless the config pins its sha256 as a challenge file: the challenge
# directory holds the same Helper.vo.
cp "$d/norec/sol/Helper.vo" "$d/norec/ch/"
cat > "$d/norec-pin.json" <<EOF
{"theorems": [{"name": "Top.A.thm"}],
 "challenge_files": [{"path": "A.vo", "sha256": "$(digest norec/ch/A.vo)"},
                     {"path": "Helper.vo", "sha256": "$(digest norec/ch/Helper.vo)"}]}
EOF
ran '-norec Top.A, Helper.vo pinned' norec norec-pin.json
holds '-norec Top.A, Helper.vo pinned' '"name":"Top.A.thm","verdict":"pass"' '"admitted":[]}'
# A challenge file pins the file at its own path below the challenge
# directory, the two compared by real path: an entry for another path pins
# nothing, not even one for a hard link to that file.
mkdir "$d/link"
ln "$d/norec/ch/Helper.vo" "$d/link/Helper.vo"
cat > "$d/norec-link.json" <<EOF
{"theorems": [{"name": "Top.A.thm"}],
 "challenge_files": [{"path": "A.vo", "sha256": "$(digest norec/ch/A.vo)"},
                     {"path": "$d/link/Helper.vo", "sha256": "$(digest link/Helper.vo)"}]}
EOF
refused 'The solution library Top.Helper was loaded without a check' norec norec-link.json

# A library that one given with -admit depends on is loaded without a check
# too, and is not exempt: Top.Base, which Top.Mid depends on, is refused
# unless -admit names it as well. The verdict lists each library given with
# -admit once, in the order given.
compile norec/deep Base.v <<'EOF'
Definition b : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
compile norec/deep Mid.v <<'EOF'
Require Top.Base.
Definition h : forall A : Prop, forall _ : A, A := Top.Base.b.
EOF
compile norec/deep A.v <<'EOF'
Require Top.Mid.
Definition thm : forall A : Prop, forall _ : A, A := Top.Mid.h.
EOF
deep() { # [rocqchk options]
  chk -Q "$d/norec/deep" Top "$@" -compare "$d/norec.json" -challenge "$d/norec/ch" \
    -compare-out "$out" Top.A
}
refused 'The solution library Top.Base was loaded without a check' deep -admit Top.Mid
ran '-admit Top.Mid -admit Top.Base' deep -admit Top.Mid -admit Top.Base -admit Top.Mid
holds '-admit Top.Mid -admit Top.Base' '"name":"Top.A.thm","verdict":"pass"' \
  '"admitted":["Top.Mid","Top.Base"]}'

#### A pre-checked library, Top.P.Q: the solution may not change it, the
#### config pins its digest, and it is not compared. Its axiom g is permitted.

compile pre/ch P/Q.v -allow-rewrite-rules <<'EOF'
Axiom g : forall A : Prop, A.
(* A rewrite rule of a pre-checked library fails no theorem. *)
Symbol s : Prop.
Rewrite Rule r := s => (forall A : Prop, forall _ : A, A).
EOF
compile pre/ch P.v <<'EOF'
Definition harmless := Prop.
EOF
compile pre/ch A.v <<'EOF'
Require Top.P.
Require Top.P.Q.
Theorem thm : forall A : Prop, A.
Proof. Admitted.
EOF

# The config names g as a theorem too, with a permitted list of its own that
# replaces the top-level one, and gives a challenge file by its absolute path.
pre_config() { # <sha256 of the solution's P/Q.vo>
  cat <<EOF
{"theorems": [{"name": "Top.A.thm"}, {"name": "Top.P.Q.g", "permitted_axioms": []}],
 "permitted_axioms": ["Top.P.Q.g"],
 "prechecked": [{"library": "Top.P.Q", "sha256": "$1"}],
 "challenge_files": [{"path": "$d/pre/ch/P.vo", "sha256": "$(digest pre/ch/P.vo)"},
                     {"path": "A.vo", "sha256": "$(digest pre/ch/A.vo)"}]}
EOF
}
pre_config "$(digest pre/ch/P/Q.vo)" > "$d/pre.json"

for t in honest forged; do
  mkdir -p "$d/pre/$t/P"
  cp "$d/pre/ch/P/Q.vo" "$d/pre/$t/P/"
done
compile pre/honest P.v < "$d/pre/ch/P.v"
compile pre/honest A.v <<'EOF'
Require Top.P.
Require Top.P.Q.
Definition thm : forall A : Prop, A := Top.P.Q.g.
EOF
# The pre-checked library, which the option admits itself, is not one given
# with -admit.
verdict pre/honest pre.json \
  '"name":"Top.A.thm","verdict":"pass","reason":"","axioms":["Top.P.Q.g"]' \
  '"name":"Top.P.Q.g","verdict":"fail","reason":"the axiom Top.P.Q.g is not permitted"' \
  '"admitted":[]}'

# A module Q of Top.P, whose axiom g prints Top.P.Q.g too.
compile pre/forged P.v <<'EOF'
Definition harmless := Prop.
Module Q.
  Axiom g : forall A : Prop, A.
End Q.
EOF
compile pre/forged A.v <<'EOF'
Require Top.P.
Definition thm : forall A : Prop, A := Top.P.Q.g.
EOF
verdict pre/forged pre.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the axiom Top.P.Q.g is not the challenge' \
  '"name":"Top.P.Q.g","verdict":"fail","reason":"the solution declares 2 constants that print the theorem'

# A solution built on another Top.P.Q: refused under the challenge's digest,
# and under its own, for the two sides then depend on two libraries of one
# name.
{ cat "$d/pre/ch/P/Q.v"; echo 'Definition extra := Prop.'; } | compile pre/other P/Q.v -allow-rewrite-rules
compile pre/other P.v < "$d/pre/ch/P.v"
compile pre/other A.v < "$d/pre/honest/A.v"
refused 'The pre-checked library Top.P.Q is' compare pre/other pre.json
pre_config "$(digest pre/other/P/Q.vo)" > "$d/pre-other.json"
refused 'The library Top.A depends on the pre-checked library Top.P.Q with a different digest' \
  compare pre/other pre-other.json

# A pre-checked library, Top.P.Q, that depends on another library of the
# tree, Top.D. The config pins the bytes of Top.P.Q, which state a digest for
# Top.D; a digest is what a library's own file states, so it pins nothing,
# and Top.D must be pre-checked too or pinned by its sha256 as a challenge
# file. A kernel check of Top.D is not enough: Top.P.Q was not checked
# against it.
compile predep/ch D.v <<'EOF'
Definition d := Prop.
EOF
compile predep/ch P/Q.v <<'EOF'
Require Top.D.
Definition q := Top.D.d.
EOF
compile predep/ch A.v <<'EOF'
Require Top.P.Q.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
mkdir -p "$d/predep/sol/P"
cp "$d/predep/ch/D.vo" "$d/predep/sol/"
cp "$d/predep/ch/P/Q.vo" "$d/predep/sol/P/"
compile predep/sol A.v <<'EOF'
Require Top.P.Q.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
prechecked() { # <library> <file whose sha256 the config pins>
  printf '{"library": "%s", "sha256": "%s"}' "$1" "$(digest "$2")"
}
config predep "\"prechecked\": [$(prechecked Top.P.Q predep/ch/P/Q.vo)]," > "$d/predep.json"
# Top.A and Top.D are both checked: refused all the same.
refused 'The pre-checked library Top.P.Q depends on the library Top.D' compare predep/sol predep.json
# Only Top.A is checked, and Top.D is loaded without a check, as a
# dependency of Top.P.Q.
predep() { # <config>
  chk -Q "$d/predep/sol" Top -compare "$d/$1" -challenge "$d/predep/ch" -compare-out "$out" Top.A
}
refused 'The pre-checked library Top.P.Q depends on the library Top.D' predep predep.json
config predep "\"prechecked\": [$(prechecked Top.P.Q predep/ch/P/Q.vo),
  $(prechecked Top.D predep/ch/D.vo)]," > "$d/predep-both.json"
ran 'Top.A with predep-both.json' predep predep-both.json
holds 'Top.A with predep-both.json' '"name":"Top.A.thm","verdict":"pass"'
# Top.D pinned by its sha256 as a challenge file, and not pre-checked.
cat > "$d/predep-pin.json" <<EOF
{"theorems": [{"name": "Top.A.thm"}], "prechecked": [$(prechecked Top.P.Q predep/ch/P/Q.vo)],
 "challenge_files": [{"path": "A.vo", "sha256": "$(digest predep/ch/A.vo)"},
                     {"path": "D.vo", "sha256": "$(digest predep/ch/D.vo)"}]}
EOF
ran 'Top.A with predep-pin.json' predep predep-pin.json
holds 'Top.A with predep-pin.json' '"name":"Top.A.thm","verdict":"pass"'

# A sort s of Top.D that only the pre-checked library Top.P.Q names: box
# lives in it. Top.D is pinned by its sha256 as a challenge file. unbox
# eliminates box into Prop, which the challenge's s does not allow, so an
# honest solution leaves unbox admitted. A solution that adds s -> Prop
# proves it. No compared declaration names s, and the constraint is
# compared all the same: a sort of a library that a pre-checked one rests
# on is renamed to itself.
compile presort/ch D.v <<'EOF'
Sort s.
EOF
compile presort/ch P/Q.v <<'EOF'
Require Top.D.
Unset Elimination Schemes.
Inductive box (A : Prop) : Univ@{Top.D.s;_} := mk : forall _ : A, box A.
EOF
compile presort/ch A.v <<'EOF'
Require Top.P.Q.
Lemma unbox : forall A : Prop, forall _ : Top.P.Q.box A, A.
Proof. Admitted.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
cat > "$d/presort.json" <<EOF
{"theorems": [{"name": "Top.A.thm"}, {"name": "Top.A.unbox"}],
 "prechecked": [$(prechecked Top.P.Q presort/ch/P/Q.vo)],
 "challenge_files": [{"path": "A.vo", "sha256": "$(digest presort/ch/A.vo)"},
                     {"path": "D.vo", "sha256": "$(digest presort/ch/D.vo)"}]}
EOF
for t in honest bad; do
  mkdir -p "$d/presort/$t/P"
  cp "$d/presort/ch/D.vo" "$d/presort/$t/"
  cp "$d/presort/ch/P/Q.vo" "$d/presort/$t/P/"
done
compile presort/honest A.v <<'EOF'
Require Top.P.Q.
Lemma unbox : forall A : Prop, forall _ : Top.P.Q.box A, A.
Proof. Admitted.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict presort/honest presort.json '"name":"Top.A.thm","verdict":"pass"' \
  '"name":"Top.A.unbox","verdict":"fail","reason":"the axiom Top.A.unbox is not permitted"' \
  '"declarations":[]'
compile presort/bad A.v <<'EOF'
Require Top.D.
Require Top.P.Q.
Constraint Top.D.s -> Prop.
Definition unbox : forall A : Prop, forall _ : Top.P.Q.box A, A :=
  fun A b => match b with Top.P.Q.mk _ a => a end.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => unbox A (Top.P.Q.mk A a).
EOF
verdict presort/bad presort.json \
  '"name":"Top.A.unbox","verdict":"fail","reason":"the solution has an elimination constraint the challenge does not: the constraint Top.D.0 -> Prop' \
  '{"name":"<qualities>","reason":"the solution has an elimination constraint the challenge does not: the constraint Top.D.0 -> Prop'

#### The bytes of a library read without a check. With -compare, the sha256
#### of each pre-checked library is compared before any library is read,
#### and every library either side reads is validated as it is read.

# A .vo file starts with a header of 16 bytes. Its first segment follows:
# OCaml's marshal header of 20 bytes, whose second word is the length of the
# data after it, then that data, then the data's MD5. od may end its output
# with an empty line (BSD od does), so awk folds every byte it reads into one
# number.
number_at() { # <file> <offset> <count>: the big-endian number of <count> bytes at <offset>
  od -An -tu1 -j"$2" -N"$3" "$1" | awk '{ for (i = 1; i <= NF; i++) n = n * 256 + $i } END { print n }'
}
seg_len() { number_at "$1" 20 4; } # <file>: the length of the data of its first segment
overwrite() { # <file> <offset>: 16 bytes 0xff from <offset> on
  printf '\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377' |
    dd of="$1" bs=1 seek="$2" conv=notrunc 2> /dev/null
}

# A pre-checked library, Top.P.Q, whose file holds other bytes and that no
# checked library Requires: the challenge's file, with the start of the data
# of its first segment overwritten. It is refused by its sha256, and nothing
# reads those bytes.
compile prebad/ch A.v <<'EOF'
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
compile prebad/sol A.v <<'EOF'
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
mkdir "$d/prebad/sol/P"
cp "$d/pre/ch/P/Q.vo" "$d/prebad/sol/P/"
overwrite "$d/prebad/sol/P/Q.vo" 36
config prebad "\"prechecked\": [$(prechecked Top.P.Q pre/ch/P/Q.vo)]," > "$d/prebad.json"
refused 'The pre-checked library Top.P.Q is' compare prebad/sol prebad.json
# prebad/two and prebad/pin are both bound to Top, and the load path
# searches prebad/pin first: Top.P.Q resolves to its copy of the pinned
# file, whose sha256 is compared before any library is read. The command
# line names prebad/two's P/Q.vo, another library of that name, which the
# loader then reads instead: that file is refused by its sha256 as well.
mkdir -p "$d/prebad/pin/P"
cp "$d/pre/ch/P/Q.vo" "$d/prebad/pin/P/"
compile prebad/two A.v < "$d/prebad/sol/A.v"
compile prebad/two P/Q.v <<'EOF'
Definition q := Prop.
EOF
refused "The pre-checked library Top.P.Q is $d/prebad/two/P/Q.vo," \
  compare prebad/two prebad.json -Q "$d/prebad/pin" Top "$d/prebad/two/P/Q.vo"

# Top.Helper, given with -admit, is loaded without a check and validated all
# the same: here the data of its first segment no longer has the MD5 that
# follows it, which only a read that validates compares.
mkdir "$d/norec/md5"
cp "$d/norec/sol/A.vo" "$d/norec/sol/Helper.vo" "$d/norec/md5/"
overwrite "$d/norec/md5/Helper.vo" $((36 + $(seg_len "$d/norec/md5/Helper.vo")))
refused 'Corrupted file' chk -Q "$d/norec/md5" Top -compare "$d/norec.json" \
  -challenge "$d/norec/ch" -compare-out "$out" -norec Top.A -admit Top.Helper

# The challenge side too: the challenge directory of nodefs lacks Defs.vo,
# which its A.vo depends on, and the load path finds the solution's, which
# only the challenge reads (the solution's A.v does not Require it) and
# whose MD5 does not match. It is refused as it is read, before the test of
# where it lies.
compile nodefs/md5 A.v <<'EOF'
Definition thm := Prop.
EOF
cp "$d/main/ch/Defs.vo" "$d/nodefs/md5/"
overwrite "$d/nodefs/md5/Defs.vo" $((36 + $(seg_len "$d/nodefs/md5/Defs.vo")))
refused 'Corrupted file' chk -Q "$d/nodefs/md5" Top -compare "$d/nodefs.json" \
  -challenge "$d/nodefs/ch" -compare-out "$out" Top.A

# The last 8 bytes of the header give the position of the summary, which
# lists each segment: the length of its name (4 bytes), the name, the
# segment's position (8 bytes), its length (8 bytes) and its MD5, which also
# follows its data. The MD5 of the segment named library is the library's
# digest, the one a library records for each library it depends on.
segment_md5() { # <file> <segment>: sets summary_md5 and data_md5, the offsets of its MD5
  local f=$1 at n nlen pos len
  at=$(number_at "$f" 8 8)
  n=$(number_at "$f" "$at" 4)
  at=$((at + 4))
  while [ "$n" -gt 0 ]; do
    nlen=$(number_at "$f" "$at" 4)
    if [ "$(dd if="$f" bs=1 skip=$((at + 4)) count="$nlen" 2> /dev/null)" = "$2" ]; then
      pos=$(number_at "$f" $((at + 4 + nlen)) 8)
      len=$(number_at "$f" $((at + 12 + nlen)) 8)
      summary_md5=$((at + 20 + nlen))
      data_md5=$((pos + len))
      return
    fi
    at=$((at + 36 + nlen))
    n=$((n - 1))
  done
  fail "$f has no segment $2"
}
copy_md5() { # <from> <offset> <to> <offset>: 16 bytes
  dd if="$1" bs=1 skip="$2" count=16 2> /dev/null | dd of="$3" bs=1 seek="$4" conv=notrunc 2> /dev/null
}

# A Top.D of other bytes, made to state the digest of the challenge's: the
# MD5 of its library segment, in the summary and after the data, is the
# challenge's Top.D's, which Top.P.Q records. A read that validates compares
# those two copies with each other, and the digest Top.P.Q records with the
# first, so the kernel checks this Top.D and takes it for the library that
# Top.P.Q was built against. Only the pin of Top.D by its sha256 tells the
# two files apart, and the run is refused.
compile predep/fake D.v <<'EOF'
Definition d := forall A : Prop, A.
EOF
mkdir -p "$d/predep/forged/P"
cp "$d/predep/sol/A.vo" "$d/predep/fake/D.vo" "$d/predep/forged/"
cp "$d/predep/ch/P/Q.vo" "$d/predep/forged/P/"
segment_md5 "$d/predep/ch/D.vo" library
from=$summary_md5
segment_md5 "$d/predep/forged/D.vo" library
copy_md5 "$d/predep/ch/D.vo" "$from" "$d/predep/forged/D.vo" "$summary_md5"
copy_md5 "$d/predep/ch/D.vo" "$from" "$d/predep/forged/D.vo" "$data_md5"
refused 'The pre-checked library Top.P.Q depends on the library Top.D' \
  compare predep/forged predep-pin.json

#### A -vos build holds no proof.

compile vos/ch A.v <<'EOF'
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config vos > "$d/vos.json"
# The proof uses a library of the installed load path, which both sides read.
compile vos/sol A.v <<'EOF'
Require Import Corelib.Init.Ltac.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. exact (fun A a => a). Qed.
EOF
verdict vos/sol vos.json '"name":"Top.A.thm","verdict":"pass"'
# The same file built with -vos: the solution's own check stops the run.
compile vos/vos A.v -vos < "$d/vos/sol/A.v"
mv "$d/vos/vos/A.vos" "$d/vos/vos/A.vo"
refused 'Cannot access opaque delayed proof' compare vos/vos vos.json

#### Universe constraints.

compile univ/ch A.v <<'EOF'
Universe u v w.
Constraint u < v.
Definition U := Type@{u}.
Definition V := Type@{v}.
Definition W := Type@{w}.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config univ > "$d/univ.json"
config univ '"tolerated_flags": [{"kind": "answer-universe-constraints"}],' > "$d/univ-any.json"

# helper declares a level before the challenge's: the two sides number the
# levels differently.
compile univ/honest A.v <<'EOF'
Definition helper := Type.
Universe u v w.
Constraint u < v.
Definition U := Type@{u}.
Definition V := Type@{v}.
Definition W := Type@{w}.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict univ/honest univ.json '"name":"Top.A.thm","verdict":"pass"'
verdict univ/honest univ-any.json '"name":"Top.A.thm","verdict":"pass"'
lacks answer-universe-constraints

# lift adds v <= w, which the challenge does not have.
{ cat "$d/univ/honest/A.v"; echo 'Definition lift (A : V) : W := A.'; } | compile univ/lift A.v
verdict univ/lift univ.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the solution has a universe constraint the challenge does not:' \
  '{"name":"<universes>","reason":'
verdict univ/lift univ-any.json '"name":"Top.A.thm","verdict":"pass"' \
  '{"kind":"answer-universe-constraints","object":"the constraint Top.A'

# The tolerance does not cover a constraint of the challenge that the
# solution drops.
grep -v '^Constraint' "$d/univ/honest/A.v" | compile univ/drop A.v
verdict univ/drop univ-any.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge has a universe constraint the solution does not:'

# The polymorphic context of f constrains its level i below the global level
# u, which the solution numbers differently: the constraint is compared
# through the level map. One more constraint, on another level, differs.
compile univp/ch A.v <<'EOF'
Universe u.
Polymorphic Definition f@{i | i < u} : Type@{u} := Type@{i}.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config univp > "$d/univp.json"
compile univp/honest A.v <<'EOF'
Definition helper := Type.
Universe u.
Polymorphic Definition f@{i | i < u} : Type@{u} := Type@{i}.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict univp/honest univp.json '"name":"Top.A.thm","verdict":"pass"'
compile univp/extra A.v <<'EOF'
Universe u v.
Polymorphic Definition f@{i | i < u, i < v} : Type@{u} := Type@{i}.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict univp/extra univp.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.f differs: the universe context has other constraints"'

# The context of small constrains its level i below the global level u,
# which no term of the declaration names and which the solution numbers
# differently: the constraint itself maps u. A copy whose constraint names
# v, which V has mapped, fails.
compile univs/ch A.v <<'EOF'
Universe u v.
Constraint u < v.
Definition V := Type@{v}.
Polymorphic Definition small@{i | i < u} : Type@{i+1} := Type@{i}.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config univs > "$d/univs.json"
compile univs/honest A.v <<'EOF'
Definition helper := Type.
Universe u v.
Constraint u < v.
Definition V := Type@{v}.
Polymorphic Definition small@{i | i < u} : Type@{i+1} := Type@{i}.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict univs/honest univs.json '"name":"Top.A.thm","verdict":"pass"'
sed 's/^Polymorphic Definition small@{i | i < u}/Polymorphic Definition small@{i | i < v}/' \
  "$d/univs/honest/A.v" | compile univs/other A.v
verdict univs/other univs.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.small differs'
# A copy whose context adds i < w, on a level w that nothing maps: two
# constraints where the challenge has one, which differ whatever the map
# pairs u with.
sed -e 's/^Universe u v\./Universe u v w./' \
  -e 's/^Polymorphic Definition small@{i | i < u}/Polymorphic Definition small@{i | i < u, i < w}/' \
  "$d/univs/honest/A.v" | compile univs/more A.v
verdict univs/more univs.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.small differs: the universe context has other constraints"'

# The context of small constrains i below u and w, two levels that no term
# names, so each of its constraints fits two of the solution's: nothing
# decides between them but the solution's level of the same library and
# number, which is taken once no other comparison maps the level. A copy
# whose context names v instead of w, a level that V maps and u < v
# constrains, fails; so does a copy that relates u and w, whichever way the
# map pairs them.
compile univs2/ch A.v <<'EOF'
Universe u v w.
Constraint u < v.
Definition V := Type@{v}.
Polymorphic Definition small@{i | i < u, i < w} : Type@{i+1} := Type@{i}.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config univs2 > "$d/univs2.json"
compile univs2/honest A.v <<'EOF'
Universe u v w.
Constraint u < v.
Definition V := Type@{v}.
Polymorphic Definition small@{i | i < u, i < w} : Type@{i+1} := Type@{i}.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict univs2/honest univs2.json '"name":"Top.A.thm","verdict":"pass"'
sed 's/^Polymorphic Definition small@{i | i < u, i < w}/Polymorphic Definition small@{i | i < u, i < v}/' \
  "$d/univs2/honest/A.v" | compile univs2/other A.v
verdict univs2/other univs2.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.small differs'
{ cat "$d/univs2/honest/A.v"; echo 'Constraint w < u.'; } | compile univs2/related A.v
verdict univs2/related univs2.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the solution has a universe constraint the challenge does not:'

# The first form of the limit of a tie (mirror below shows the second): the
# solution declares two levels before u and w, so it numbers them otherwise.
# Each constraint of small then fits two of the solution's, neither of which
# has the number of the challenge's level, and nothing else decides: the
# declaration is undecided, though the solution is honest, and the reason
# names a level of the challenge that it leaves unmapped. The copy that
# numbers u and w as the challenge does passes.
compile spare/ch A.v <<'EOF'
Universe u w.
Polymorphic Definition small@{i | i < u, i < w} : Type@{i+1} := Type@{i}.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config spare > "$d/spare.json"
compile spare/same A.v <<'EOF'
Universe u w.
Polymorphic Definition small@{i | i < u, i < w} : Type@{i+1} := Type@{i}.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict spare/same spare.json '"name":"Top.A.thm","verdict":"pass"'
sed 's/^Universe u w\./Universe spare1 spare2 u w./' "$d/spare/same/A.v" | compile spare/shifted A.v
verdict spare/shifted spare.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.small differs: the universe context constrains the universe Top.A:' \
  ', which no comparison has mapped"'

# The context of foo constrains the global level u below the global level w,
# and no term names either: the constraint maps both, when the solution's
# foo holds the same constraint between its levels of the same library and
# number. A copy whose foo puts w below u fails.
compile glob2/ch A.v <<'EOF'
Universe u w.
Polymorphic Definition foo@{i | u < w} : Type@{i+1} := Type@{i}.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config glob2 > "$d/glob2.json"
compile glob2/honest A.v <<'EOF'
Universe u w.
Polymorphic Definition foo@{i | u < w} : Type@{i+1} := Type@{i}.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict glob2/honest glob2.json '"name":"Top.A.thm","verdict":"pass"' '"declarations":[]'
sed 's/^Polymorphic Definition foo@{i | u < w}/Polymorphic Definition foo@{i | w < u}/' \
  "$d/glob2/honest/A.v" | compile glob2/swapped A.v
verdict glob2/swapped glob2.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.foo differs'

# A tie is taken only once the constraints decide nothing more without one.
# The context of pick holds x < y, and the solution declares y2 before y, so
# the challenge's y has the number of the solution's y2, which j < y2 bounds
# as j < y bounds y. The first tie pairs x with x, among the levels that
# i < x and i < x2 bound; x < y then pairs y with the solution's y, and the
# rest follows. A tie on j < y, taken in the same pass as the one on x,
# would pair y with the solution's y2 and fail this honest copy. The first
# tie is on x only because the constraints on i, the first bound level,
# sort before those on j: mirror below swaps i and j, and fails.
compile tie/ch A.v <<'EOF'
Universe x x2 y y2.
Polymorphic Definition pick@{i j | i < x, i < x2, x < y, j < y, j < y2} :
  Type@{max(i+1,j+1)} := forall _ : Type@{i}, Type@{j}.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config tie > "$d/tie.json"
compile tie/honest A.v <<'EOF'
Universe x x2 y2 y.
Polymorphic Definition pick@{i j | i < x, i < x2, x < y, j < y, j < y2} :
  Type@{max(i+1,j+1)} := forall _ : Type@{i}, Type@{j}.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict tie/honest tie.json '"name":"Top.A.thm","verdict":"pass"' '"declarations":[]'

# A tie on one end comes before a tie on two ends. The solution declares d
# before a, b and c, so it numbers each of them one higher than the
# challenge does, and its a < b has the numbers of the challenge's b < c.
# j < d pairs d, and then nothing decides anything without a tie. The tie on
# i < e pairs e with e; e < a, a < b and b < c then pair a, b and c, and
# i < f pairs f. A tie on two ends on b < c, which sorts before the
# constraints on i, would pair b and c with the solution's a and b, and fail
# this honest copy.
compile oneend/ch A.v <<'EOF'
Universe a b c d e f.
Polymorphic Definition foo@{i j | a < b, b < c, e < a, i < e, i < f, j < d} :
  Type@{max(i+1,j+1)} := forall _ : Type@{i}, Type@{j}.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config oneend > "$d/oneend.json"
compile oneend/honest A.v <<'EOF'
Universe d a b c e f.
Polymorphic Definition foo@{i j | a < b, b < c, e < a, i < e, i < f, j < d} :
  Type@{max(i+1,j+1)} := forall _ : Type@{i}, Type@{j}.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict oneend/honest oneend.json '"name":"Top.A.thm","verdict":"pass"' '"declarations":[]'

# The second form of the limit of a tie: pick is the context of tie with i
# and j swapped, so in the copy that declares y2 before y the first tie is on
# i < y, whose two fits are the solution's y2 and y. It pairs y with the
# solution's y2, which has the number of the challenge's y; x < y then
# stands for x < y2, which the solution's pick does not hold, and the reason
# names no level, though the solution is honest. The copy that numbers y and
# y2 as the challenge does passes.
compile mirror/ch A.v <<'EOF'
Universe x x2 y y2.
Polymorphic Definition pick@{i j | j < x, j < x2, x < y, i < y, i < y2} :
  Type@{max(i+1,j+1)} := forall _ : Type@{i}, Type@{j}.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config mirror > "$d/mirror.json"
compile mirror/same A.v <<'EOF'
Universe x x2 y y2.
Polymorphic Definition pick@{i j | j < x, j < x2, x < y, i < y, i < y2} :
  Type@{max(i+1,j+1)} := forall _ : Type@{i}, Type@{j}.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict mirror/same mirror.json '"name":"Top.A.thm","verdict":"pass"' '"declarations":[]'
sed 's/^Universe x x2 y y2\./Universe x x2 y2 y./' "$d/mirror/same/A.v" | compile mirror/shifted A.v
verdict mirror/shifted mirror.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.pick differs: the universe context has other constraints"' \
  '{"name":"Top.A.pick","reason":"the universe context has other constraints"}'

#### The type of a is the universe max(u+1, v+1), whose two levels no
#### comparison has paired yet and have the same increment: which level of
#### the solution each stands for is not decided. The declaration is compared
#### again once the others have been (the constants are compared in the
#### order their names sort), and fails if none of them pairs those levels.

compile undecided/ch A.v <<'EOF'
Universe u v.
Definition a : Type@{max(u+1,v+1)} := forall _ : Type@{u}, Type@{v}.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config undecided > "$d/undecided.json"
compile undecided/sol A.v <<'EOF'
Universe u v.
Definition a : Type@{max(u+1,v+1)} := forall _ : Type@{u}, Type@{v}.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict undecided/sol undecided.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the challenge declaration Top.A.a differs: universe ' \
  'each level of the challenge stands for is not decided'
# b, compared after a, pairs u with u, and then a pairs v with v.
compile decided/ch A.v <<'EOF'
Universe u v.
Definition a : Type@{max(u+1,v+1)} := forall _ : Type@{u}, Type@{v}.
Definition b := Type@{u}.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config decided > "$d/decided.json"
compile decided/sol A.v <<'EOF'
Universe u v.
Definition a : Type@{max(u+1,v+1)} := forall _ : Type@{u}, Type@{v}.
Definition b := Type@{u}.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict decided/sol decided.json '"name":"Top.A.thm","verdict":"pass"'

#### Elimination constraints: box lives in a sort s, which may not be
#### eliminated into Prop unless the challenge says so.

compile elim/ch A.v <<'EOF'
Unset Elimination Schemes.
Sort s.
Inductive box (A : Prop) : Univ@{s;_} := mk : forall _ : A, box A.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config elim > "$d/elim.json"
compile elim/honest A.v <<'EOF'
Unset Elimination Schemes.
Sort s.
Inductive box (A : Prop) : Univ@{s;_} := mk : forall _ : A, box A.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict elim/honest elim.json '"name":"Top.A.thm","verdict":"pass"'
compile elim/bad A.v <<'EOF'
Unset Elimination Schemes.
Sort s.
Inductive box (A : Prop) : Univ@{s;_} := mk : forall _ : A, box A.
Constraint s -> Prop.
Definition unbox (A : Prop) (b : box A) : A := match b with mk _ a => a end.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => unbox A (mk A a).
EOF
verdict elim/bad elim.json '"name":"Top.A.thm","verdict":"fail"' \
  '{"name":"<qualities>","reason":"the solution has an elimination constraint the challenge does not: the constraint Top.A.0 -> Prop'
# answer-universe-constraints does not tolerate it.
config elim '"tolerated_flags": [{"kind": "answer-universe-constraints"}],' > "$d/elim-any.json"
verdict elim/bad elim-any.json '"name":"Top.A.thm","verdict":"fail"' \
  '{"name":"<qualities>","reason":"the solution has an elimination constraint the challenge does not: the constraint Top.A.0 -> Prop'

# A library numbers its sorts in the order it declares them. A solution that
# declares a sort t of its own before s, with a constraint of its own, gives
# its s the number 1 where the challenge's s has 0: the sorts are compared
# through a map that pairs them. t, which nothing of the challenge's
# stands for, may be eliminated into Prop.
compile elim/own A.v <<'EOF'
Unset Elimination Schemes.
Sort t.
Constraint t -> Prop.
Sort s.
Inductive box (A : Prop) : Univ@{s;_} := mk : forall _ : A, box A.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => a.
EOF
verdict elim/own elim.json '"name":"Top.A.thm","verdict":"pass"'
# The same constraint on its s, numbered 1, is one on the challenge's s.
compile elim/shifted A.v <<'EOF'
Unset Elimination Schemes.
Sort t.
Sort s.
Inductive box (A : Prop) : Univ@{s;_} := mk : forall _ : A, box A.
Constraint s -> Prop.
Definition unbox (A : Prop) (b : box A) : A := match b with mk _ a => a end.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => unbox A (mk A a).
EOF
verdict elim/shifted elim.json '"name":"Top.A.thm","verdict":"fail"' \
  '{"name":"<qualities>","reason":"the solution has an elimination constraint the challenge does not: the constraint Top.A.1 -> Prop'

# Two sorts, which the solution declares in the other order: each stands for
# the challenge's sort of its name, the constraint s -> Prop included.
compile elims/ch A.v <<'EOF'
Unset Elimination Schemes.
Sort s.
Sort t.
Inductive box (A : Prop) : Univ@{s;_} := mk : forall _ : A, box A.
Inductive tbox (A : Prop) : Univ@{t;_} := tmk : forall _ : A, tbox A.
Constraint s -> Prop.
Theorem thm : forall A : Prop, forall _ : box A, A.
Proof. Admitted.
EOF
config elims > "$d/elims.json"
compile elims/swapped A.v <<'EOF'
Unset Elimination Schemes.
Sort t.
Sort s.
Inductive box (A : Prop) : Univ@{s;_} := mk : forall _ : A, box A.
Inductive tbox (A : Prop) : Univ@{t;_} := tmk : forall _ : A, tbox A.
Constraint s -> Prop.
Definition unbox (A : Prop) (b : box A) : A := match b with mk _ a => a end.
Definition thm : forall A : Prop, forall _ : box A, A := unbox.
EOF
verdict elims/swapped elims.json '"name":"Top.A.thm","verdict":"pass"'

# A challenge whose box may be eliminated into Prop, and a solution that
# drops the constraint.
compile elimc/ch A.v <<'EOF'
Unset Elimination Schemes.
Sort s.
Inductive box (A : Prop) : Univ@{s;_} := mk : forall _ : A, box A.
Constraint s -> Prop.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config elimc > "$d/elimc.json"
compile elimc/drop A.v < "$d/elim/honest/A.v"
verdict elimc/drop elimc.json '"name":"Top.A.thm","verdict":"fail"' \
  '{"name":"<qualities>","reason":"the challenge has an elimination constraint the solution does not: the constraint Top.A.0 -> Prop'

# The sort s and box in a pre-checked library outside the challenge's root,
# Vendor.S: a constraint that the solution adds on that sort is compared as
# well.
mkdir "$d/elimlib"
cat > "$d/elimlib/S.v" <<'EOF'
Unset Elimination Schemes.
Sort s.
Inductive box (A : Prop) : Univ@{s;_} := mk : forall _ : A, box A.
EOF
$coqc -noinit -native-compiler no -Q "$d/elimlib" Vendor "$d/elimlib/S.v"
compile elimv/ch A.v -Q "$d/elimlib" Vendor <<'EOF'
Require Vendor.S.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
config elimv "\"prechecked\": [$(prechecked Vendor.S elimlib/S.vo)]," > "$d/elimv.json"
compile elimv/bad A.v -Q "$d/elimlib" Vendor <<'EOF'
Require Vendor.S.
Constraint Vendor.S.s -> Prop.
Definition unbox (A : Prop) (b : Vendor.S.box A) : A := match b with Vendor.S.mk _ a => a end.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => unbox A (Vendor.S.mk A a).
EOF
ran elimv/bad compare elimv/bad elimv.json -Q "$d/elimlib" Vendor
holds elimv/bad '"name":"Top.A.thm","verdict":"fail"' \
  '{"name":"<qualities>","reason":"the solution has an elimination constraint the challenge does not: the constraint Vendor.S.0 -> Prop'

#### Relaxed typing conditions: the challenge declares seq under
#### definitional UIP, which lets a match on seq return a Prop.

compile uip/ch A.v <<'EOF'
Unset Elimination Schemes.
Set Definitional UIP.
Inductive seq {A : Type} (a : A) : forall _ : A, SProp := srefl : seq a a.
Unset Definitional UIP.
Theorem thm : forall A : Prop, forall _ : A, A.
Proof. Admitted.
EOF
# seq has an index, so it also rests on indices not mattering, which both
# configs tolerate on every object.
config uip '"tolerated_flags": [{"kind": "indices-not-mattering"}],' > "$d/uip.json"
config uip '"tolerated_flags": [{"kind": "indices-not-mattering"},
  {"kind": "uip", "object": "Top.A.seq"}, {"kind": "uip", "object": "Top.A.seq2"}],' > "$d/uip-named.json"

# A proof through the challenge's seq.
compile uip/seq A.v <<'EOF'
Unset Elimination Schemes.
Set Definitional UIP.
Inductive seq {A : Type} (a : A) : forall _ : A, SProp := srefl : seq a a.
Unset Definitional UIP.
Definition cast (A : Prop) (e : seq A A) (a : A) : A := match e with srefl _ => a end.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => cast A (srefl A) a.
EOF
verdict uip/seq uip.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the relaxed typing flag uip on Top.A.seq is not tolerated'
verdict uip/seq uip-named.json '"name":"Top.A.thm","verdict":"pass"' '{"kind":"uip","object":"Top.A.seq"}'

# A proof through seq2, the solution's own: a flag tolerated on a name is
# tolerated only on the challenge's declaration of that name.
compile uip/seq2 A.v <<'EOF'
Unset Elimination Schemes.
Set Definitional UIP.
Inductive seq {A : Type} (a : A) : forall _ : A, SProp := srefl : seq a a.
Inductive seq2 {A : Type} (a : A) : forall _ : A, SProp := srefl2 : seq2 a a.
Unset Definitional UIP.
Definition cast2 (A : Prop) (e : seq2 A A) (a : A) : A := match e with srefl2 _ => a end.
Definition thm : forall A : Prop, forall _ : A, A := fun A a => cast2 A (srefl2 A) a.
EOF
verdict uip/seq2 uip-named.json \
  '"name":"Top.A.thm","verdict":"fail","reason":"the relaxed typing flag uip on Top.A.seq2 is not tolerated: the config tolerates it on that name'
