#!/usr/bin/env bash
# The Skip Qed Typecheck flag, set with -set "Skip Qed Typecheck" or with
# "Set Skip Qed Typecheck.", skips the kernel typing of a Qed proof as the
# -skip-qed-typecheck option does: an ill-typed proof compiles, Print
# Assumptions reports it in its own file and in a file that requires it, and
# rocqchk rejects the library. With neither, and after "Unset Skip Qed
# Typecheck.", Qed rejects the proof. -skip-qed-typecheck applies to every
# proof, so "Unset Skip Qed Typecheck." does not turn it off.
set -euo pipefail

export PATH="$BIN:$PATH"
workdir=$(mktemp -d)
trap 'rm -rf "$workdir"' EXIT

fail() { echo "$*" >&2; exit 1; }

proof='Lemma bad : False.
Proof. exact_no_check I. Qed.
Print Assumptions bad.'

expected='Axioms:
bad has an opaque proof not checked by the kernel.'

# case directory, extra rocq c arguments, lines before the proof
compile() {
  local dir="$workdir/$1" args=$2 pre=$3
  mkdir -p "$dir"
  printf '%s%s\n' "$pre" "$proof" > "$dir/bad.v"
  # $args is split on purpose; the quoted flag name is passed as one word.
  eval "rocq c -q $args -R \"\$dir\" Top \"\$dir/bad.v\"" > "$dir/compile.out" 2>&1
}

skipped() {
  local case=$1 dir="$workdir/$1"
  compile "$@" || { cat "$dir/compile.out" >&2; fail "$case: the ill-typed proof did not compile"; }
  [ "$(cat "$dir/compile.out")" = "$expected" ] ||
    { cat "$dir/compile.out" >&2; fail "$case: Print Assumptions does not report the unchecked proof"; }
  printf 'Require Top.bad.\nPrint Assumptions Top.bad.bad.\n' > "$dir/use.v"
  rocq c -q -R "$dir" Top "$dir/use.v" > "$dir/use.out" 2>&1 ||
    { cat "$dir/use.out" >&2; fail "$case: a file that requires the library does not compile"; }
  grep -qx 'Axioms:' "$dir/use.out" && grep -qx '.*bad has an opaque proof not checked by the kernel\.' "$dir/use.out" ||
    { cat "$dir/use.out" >&2; fail "$case: the library does not record the unchecked proof"; }
  if rocqchk -silent -o -R "$dir" Top -norec Top.bad > "$dir/check.out" 2>&1; then
    cat "$dir/check.out" >&2; fail "$case: rocqchk accepted the ill-typed proof"
  fi
  grep -q 'Type error' "$dir/check.out" ||
    { cat "$dir/check.out" >&2; fail "$case: rocqchk did not reject the proof with a type error"; }
}

refused() {
  local case=$1 dir="$workdir/$1"
  if compile "$@"; then
    cat "$dir/compile.out" >&2; fail "$case: the ill-typed proof compiled"
  fi
  [ ! -e "$dir/bad.vo" ] || fail "$case: a library was written"
}

skipped option '-skip-qed-typecheck' ''
skipped set '-set "Skip Qed Typecheck"' ''
skipped inline '' 'Set Skip Qed Typecheck.
'
refused none '' ''
refused unset '-set "Skip Qed Typecheck"' 'Unset Skip Qed Typecheck.
'
skipped option_unset '-skip-qed-typecheck' 'Unset Skip Qed Typecheck.
'

# Both command-line spellings write the same library. The library records
# where its file is, so both compile the same file.
same="$workdir/same"
mkdir "$same"
printf '%s\n' "$proof" > "$same/bad.v"
rocq c -q -skip-qed-typecheck -R "$same" Top "$same/bad.v" > /dev/null
mv "$same/bad.vo" "$same/option.vo"
rocq c -q -set "Skip Qed Typecheck" -R "$same" Top "$same/bad.v" > /dev/null
cmp "$same/option.vo" "$same/bad.vo" ||
  fail "-skip-qed-typecheck and -set \"Skip Qed Typecheck\" wrote different libraries"
