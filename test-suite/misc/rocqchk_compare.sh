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
stale='{"format":1,"theorems":[{"name":"Top.A.thm","verdict":"pass","reason":"","axioms":[],"flags":[]}],"declarations":[]}'

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

# A run that writes a verdict: it exits 0 and the verdict file holds each
# <text>.
verdict() { # <tree> <config> <text>...
  local run="$1 with $2" text
  rm -f "$out"
  compare "$1" "$2" || fail "$run: exit $?"
  [ -f "$out" ] || fail "$run: no verdict file"
  shift 2
  for text in "$@"; do
    grep -qF -- "$text" "$out" || fail "$run: the verdict does not hold $text"
  done
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
verdict main/honest main.json \
  '{"format":1,"theorems":[{"name":"Top.A.thm","verdict":"pass","reason":"","axioms":[],"flags":[]},' \
  '{"name":"Top.A.other","verdict":"pass","reason":"","axioms":[],"flags":[]}],"declarations":[]}'

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

# A -Q of the empty root, or of a top-level name of the installed load path.
mkdir "$d/empty"
refused 'is bound to the empty root' compare main/honest main.json -Q "$d/empty" ""
refused 'is bound to Corelib, a name the installed load path serves' \
  compare main/honest main.json -Q "$d/empty" Corelib

# A library outside the challenge's roots and not pre-checked: from another
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
verdict pre/honest pre.json \
  '"name":"Top.A.thm","verdict":"pass","reason":"","axioms":["Top.P.Q.g"]' \
  '"name":"Top.P.Q.g","verdict":"fail","reason":"the axiom Top.P.Q.g is not permitted"'

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

#### Elimination constraints: box lives in a sort s of the challenge's own,
#### which may not be eliminated into Prop.

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
  '{"name":"<qualities>","reason":"the solution has an elimination constraint the challenge does not:'

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
