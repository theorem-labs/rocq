#!/usr/bin/env bash
# A control that observes the error or the result of the command it wraps and
# then discards its effect (Fail, Succeed) sees the same Qed as without the
# skip: the kernel checks the proof in full, so the file compiles with the
# same status and the same output with -skip-qed-typecheck, with
# -set "Skip Qed Typecheck" and after "Set Skip Qed Typecheck." as it does
# without them. The skip still applies to a Qed outside such a control.
set -euo pipefail

export PATH="$BIN:$PATH"
workdir=$(mktemp -d)
trap 'rm -rf "$workdir"' EXIT

fail() { echo "$*" >&2; exit 1; }

bad='Lemma discarded_bad : False.
Proof. exact_no_check I.'
good='Lemma kept_good : True.
Proof. exact I.'

# Every arm compiles the same path, so a message that names the file reads the
# same, and every arm's first line is one line, so a message that names a line
# reads the same too.
compile() { # case arm
  local arm=$2 dir="$workdir/$1" rc=0
  local -a args=()
  case $arm in
    plain) printf '(* no skip *)\n' > "$dir/case.v";;
    option) args=(-skip-qed-typecheck); printf '(* option *)\n' > "$dir/case.v";;
    set) args=(-set "Skip Qed Typecheck"); printf '(* set *)\n' > "$dir/case.v";;
    inline) printf 'Set Skip Qed Typecheck.\n' > "$dir/case.v";;
    *) fail "unknown arm $arm";;
  esac
  cat "$dir/body.v" >> "$dir/case.v"
  # -test-mode prints the message Fail caught, which rocq compile is quiet
  # about, so the comparison below reads it.
  rocq c -q -test-mode ${args[@]+"${args[@]}"} -R "$dir" Top "$dir/case.v" \
    > "$dir/$arm.out" 2>&1 || rc=$?
  printf '%s\n' "$rc" > "$dir/$arm.rc"
  # A Redirect case writes here, and the next arm would overwrite it.
  if [ -e "$dir/redirected.out" ]; then mv "$dir/redirected.out" "$dir/$arm.redirected"; fi
}

# The three skip arms must agree with the arm that does not skip, in exit
# status and in output.
same() { # case expected-status body...
  local case=$1 expected=$2 arm
  shift 2
  mkdir -p "$workdir/$case"
  printf '%s\n' "$@" > "$workdir/$case/body.v"
  for arm in plain option set inline; do compile "$case" "$arm"; done
  [ "$(cat "$workdir/$case/plain.rc")" = "$expected" ] ||
    { cat "$workdir/$case/plain.out" >&2
      fail "$case: exit status $(cat "$workdir/$case/plain.rc") without the skip, expected $expected"; }
  for arm in option set inline; do
    [ "$(cat "$workdir/$case/$arm.rc")" = "$expected" ] ||
      { cat "$workdir/$case/$arm.out" >&2
        fail "$case/$arm: exit status $(cat "$workdir/$case/$arm.rc") with the skip, $expected without it"; }
    diff -u "$workdir/$case/plain.out" "$workdir/$case/$arm.out" >&2 ||
      fail "$case/$arm: the output with the skip differs from the output without it"
  done
}

says() { # case text
  grep -qF "$2" "$workdir/$1/plain.out" ||
    { cat "$workdir/$1/plain.out" >&2; fail "$1: the output does not say \"$2\""; }
}

# (a) Fail Qed on an ill-typed proof: the error is caught, Abort drops the
# proof, and the file compiles.
same fail_bad 0 "$bad" 'Fail Qed.' 'Abort.' "$good" 'Qed.'
says fail_bad 'The command has indeed failed with message:'

# (b) Succeed Qed on an ill-typed proof: the error is not caught, so the file
# does not compile.
same succeed_bad 1 "$bad" 'Succeed Qed.' 'Abort.'
says succeed_bad 'The term "I" has type "True"'

# Save closes a proof the same way, so the two controls read its verdict too.
same fail_save_bad 0 "$bad" 'Fail Save other_name.' 'Abort.'
says fail_save_bad 'The command has indeed failed with message:'
same succeed_save_bad 1 "$bad" 'Succeed Save other_name.' 'Abort.'

# (c) the controls on a well-typed proof.
same fail_good 1 "$good" 'Fail Qed.' 'Abort.'
says fail_good 'The command has not failed!'
same succeed_good 0 "$good" 'Succeed Qed.' 'Qed.'

# (d) the other controls, which keep the effect of the command they wrap, and
# the two that discard it nested in each other.
same fail_succeed_bad 0 "$bad" 'Fail Succeed Qed.' 'Abort.'
says fail_succeed_bad 'The command has indeed failed with message:'
same succeed_fail_bad 0 "$bad" 'Succeed Fail Qed.' 'Abort.'
says succeed_fail_bad 'The command has indeed failed with message:'
# The inner Fail catches the error of Qed, so the outer one has nothing to
# catch and the file does not compile.
same fail_fail_bad 1 "$bad" 'Fail Fail Qed.' 'Abort.'
says fail_fail_bad 'The command has not failed!'
same timeout_fail_bad 0 "$bad" 'Timeout 600 Fail Qed.' 'Abort.'
says timeout_fail_bad 'The command has indeed failed with message:'
same redirect_fail_bad 0 "$bad" \
  "Redirect \"$workdir/redirect_fail_bad/redirected\" Fail Qed." 'Abort.'
# Redirect sends the caught message to the file, so compare the file too.
# The file is absent when the arm wrote none, so read it only if it is there.
grep -qF 'The command has indeed failed with message:' "$workdir/redirect_fail_bad/plain.redirected" ||
  { cat "$workdir/redirect_fail_bad/plain.redirected" >&2 || true
    fail "redirect_fail_bad: the redirected output does not report the caught error"; }
for arm in option set inline; do
  diff -u "$workdir/redirect_fail_bad/plain.redirected" "$workdir/redirect_fail_bad/$arm.redirected" >&2 ||
    fail "redirect_fail_bad/$arm: the redirected output with the skip differs from the one without it"
done

# (e) the skip still applies to a Qed no control discards: the file compiles
# with the skip and not without it.
skips() { # case body...
  local case=$1 arm
  shift
  mkdir -p "$workdir/$case"
  printf '%s\n' "$@" > "$workdir/$case/body.v"
  for arm in plain option set inline; do compile "$case" "$arm"; done
  [ "$(cat "$workdir/$case/plain.rc")" = 1 ] ||
    { cat "$workdir/$case/plain.out" >&2
      fail "$case: the ill-typed proof compiled without the skip"; }
  for arm in option set inline; do
    [ "$(cat "$workdir/$case/$arm.rc")" = 0 ] ||
      { cat "$workdir/$case/$arm.out" >&2
        fail "$case/$arm: the skip did not apply"; }
  done
}

# The force ends with the control that raised through it.
skips scoped "$bad" 'Fail Qed.' 'Abort.' \
  'Lemma bad : False.' 'Proof. exact_no_check I. Qed.' 'Print Assumptions bad.'
for arm in option set inline; do
  grep -qx 'bad has an opaque proof not checked by the kernel.' "$workdir/scoped/$arm.out" ||
    { cat "$workdir/scoped/$arm.out" >&2
      fail "scoped/$arm: Print Assumptions does not report the unchecked proof"; }
done

# It ends with the control that returned through it too.
skips after_succeed "$good" 'Succeed Qed.' 'Qed.' \
  'Lemma bad : False.' 'Proof. exact_no_check I. Qed.'

# A control that keeps the effect of the command never sets the force, so the
# skip still applies under it. Time prints a duration and Redirect takes the
# output away, so these read the status alone.
skips time_bad "$bad" 'Time Qed.'
skips timeout_bad "$bad" 'Timeout 600 Qed.'
skips redirect_bad "$bad" "Redirect \"$workdir/redirect_bad/redirected\" Qed."
