#!/usr/bin/env bash
# A control that observes the error or the result of the command it wraps and
# then discards its effect (Fail, Succeed) sees the same Qed as without the
# skip: the kernel checks the proof in full, so the file compiles with the
# same status and the same output with -skip-qed-typecheck, with
# -set "Skip Qed Typecheck" and after "Set Skip Qed Typecheck." as it does
# without them. A command that rolls the document back past a proof the
# kernel did not check runs that check too, so the file stops with the same
# status and with the error Qed raises without the skip. The skip still
# applies to a Qed no command discards.
set -euo pipefail

export PATH="$BIN:$PATH"
workdir=$(mktemp -d)
trap 'rm -rf "$workdir"' EXIT

fail() { echo "$*" >&2; exit 1; }

bad='Lemma discarded_bad : False.
Proof. exact_no_check I.'
good='Lemma kept_good : True.
Proof. exact I.'
kernel_error='The term "I" has type "True" while it is expected to have type "False".'

# Options every arm of the next case takes, for a case that needs its own.
extra=()

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
  rocq c -q -test-mode ${extra[@]+"${extra[@]}"} ${args[@]+"${args[@]}"} \
    -R "$dir" Top "$dir/case.v" > "$dir/$arm.out" 2>&1 || rc=$?
  printf '%s\n' "$rc" > "$dir/$arm.rc"
  # A Redirect case writes here, and the next arm would overwrite it.
  if [ -e "$dir/redirected.out" ]; then mv "$dir/redirected.out" "$dir/$arm.redirected"; fi
}

build() { # case body...
  local case=$1 arm
  shift
  mkdir -p "$workdir/$case"
  printf '%s\n' "$@" > "$workdir/$case/body.v"
  for arm in plain option set inline; do compile "$case" "$arm"; done
}

# The three skip arms must agree with the arm that does not skip, in exit
# status and in output.
same() { # case expected-status body...
  local case=$1 expected=$2 arm
  shift 2
  build "$case" "$@"
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

says() { # case text [arm...], the arm that does not skip by default
  local case=$1 text=$2 arm
  shift 2
  [ $# -gt 0 ] || set -- plain
  for arm in "$@"; do
    grep -qF "$text" "$workdir/$case/$arm.out" ||
      { cat "$workdir/$case/$arm.out" >&2
        fail "$case/$arm: the output does not say \"$text\""; }
  done
}

# (a) Fail Qed on an ill-typed proof: the error is caught, Abort drops the
# proof, and the file compiles.
same fail_bad 0 "$bad" 'Fail Qed.' 'Abort.' "$good" 'Qed.'
says fail_bad 'The command has indeed failed with message:'

# (b) Succeed Qed on an ill-typed proof: the error is not caught, so the file
# does not compile.
same succeed_bad 1 "$bad" 'Succeed Qed.' 'Abort.'
says succeed_bad "$kernel_error"

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
  build "$case" "$@"
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
says scoped 'bad has an opaque proof not checked by the kernel.' option set inline

# It ends with the control that returned through it too.
skips after_succeed "$good" 'Succeed Qed.' 'Qed.' \
  'Lemma bad : False.' 'Proof. exact_no_check I. Qed.'

# A control that keeps the effect of the command never sets the force, so the
# skip still applies under it. Time prints a duration and Redirect takes the
# output away, so these read the status alone.
skips time_bad "$bad" 'Time Qed.'
skips timeout_bad "$bad" 'Timeout 600 Qed.'
skips redirect_bad "$bad" "Redirect \"$workdir/redirect_bad/redirected\" Qed."

# (f) a rollback discards a proof the kernel did not check: the check runs
# there, so the file stops with the status it has without the skip, and with
# the kernel's error. The error is raised at the command that rolls back
# rather than at the Qed, so these read the status of every arm and the
# message, not the whole output.
same_status() { # case expected-status body...
  local case=$1 expected=$2 arm
  shift 2
  build "$case" "$@"
  for arm in plain option set inline; do
    [ "$(cat "$workdir/$case/$arm.rc")" = "$expected" ] ||
      { cat "$workdir/$case/$arm.out" >&2
        fail "$case/$arm: exit status $(cat "$workdir/$case/$arm.rc"), expected $expected"; }
  done
}

rolls_back() { # case body...
  local case=$1
  shift
  same_status "$case" 1 "$@"
  says "$case" "$kernel_error" plain option set inline
}

# Reset by name, Reset Initial, and Reset of the module that holds the proof.
rolls_back reset_bad "$bad" 'Qed.' 'Reset discarded_bad.'
rolls_back reset_initial_bad "$bad" 'Qed.' 'Reset Initial.'
rolls_back reset_module_bad 'Module M.' "$bad" 'Qed.' 'End M.' 'Reset M.'

# One rollback discards three proofs: the well-typed one passes its check, and
# of the two that do not, the error is the earlier one's, as it is without the
# skip, which is what rolls_back reads.
bad2='Lemma discarded_bad2 : True.
Proof. exact_no_check 0.'
rolls_back reset_three "$good" 'Qed.' "$bad" 'Qed.' "$bad2" 'Qed.' 'Reset kept_good.'

# The stm closes a proof nested in another by discarding its declaration and
# declaring it again, so the check of such a proof runs at its Qed, even here
# where the file keeps the proof.
rolls_back nested_bad 'Set Nested Proofs Allowed.' 'Lemma outer : True.' \
  "$bad" 'Qed.' 'exact I.' 'Qed.'

# The stm reads a navigation command without its control, so Fail catches
# nothing here.
rolls_back fail_reset_bad "$bad" 'Qed.' 'Fail Reset discarded_bad.'

# (g) a navigation command that cannot roll back after a Qed is rejected
# before it discards anything, with or without the skip, and the file stops
# either way.
same_status undo_bad 1 "$bad" 'Qed.' 'Undo.'
says undo_bad 'Cannot undo.' option set inline
same_status undo_to_bad 1 "$bad" 'Qed.' 'Undo To 1.'
says undo_to_bad 'No focused proof' option set inline
same_status restart_bad 1 "$bad" 'Qed.' 'Restart.'
says restart_bad 'No focused proof' option set inline
same_status back_bad 1 "$bad" 'Qed.' 'Back.'
says back_bad 'Navigation commands forbidden in files.' option set inline

# (h) a rollback that discards a well-typed proof the kernel did not check:
# its check passes, so the file compiles with the same output as without the
# skip. A section variable, a universe-polymorphic proof and an abstract
# subproof are what the stored proof has to be prepared for.
same reset_good 0 "$good" 'Qed.' 'Reset kept_good.'
same reset_module_good 0 'Module M.' "$good" 'Qed.' 'End M.' 'Reset M.'
same reset_section_good 0 'Section S.' 'Variable n : nat.' 'Lemma good_s : n = n.' \
  'Proof. reflexivity. Qed.' 'End S.' 'Reset Initial.'
same reset_poly_good 0 'Polymorphic Lemma good_p : forall (A : Type) (x : A), x = x.' \
  'Proof. intros. reflexivity. Qed.' 'Definition use_p := good_p nat 0.' 'Reset Initial.'
same reset_abstract_good 0 'Lemma good_a : forall n : nat, n + 0 = n.' \
  'Proof. intro n. abstract (induction n; simpl; auto). Qed.' 'Reset Initial.'

# (i) a command that discards no proof leaves the skip alone: the proof
# reaches the .vo, where rocqchk checks it, and Print Assumptions reports it
# as not checked. Abort All with no proof open rolls nothing back, End keeps
# what the module holds, and Load keeps what it read.
unchecked_proof='discarded_bad has an opaque proof not checked by the kernel.'
skips abort_all_kept "$bad" 'Qed.' 'Abort All.' 'Print Assumptions discarded_bad.'
says abort_all_kept "$unchecked_proof" option set inline
skips module_kept 'Module M.' "$bad" 'Qed.' 'End M.' 'Print Assumptions M.discarded_bad.'
says module_kept "M.$unchecked_proof" option set inline
printf '%s\n' "$bad" 'Qed.' > "$workdir/loaded_bad.v"
skips load_kept "Load \"$workdir/loaded_bad\"." 'Print Assumptions discarded_bad.'
says load_kept "$unchecked_proof" option set inline

# (j) neither a proof worker nor an interactive session is a document rocq
# compile builds, and only such a document checks what it discards. With
# -async-proofs on the Qed is delegated, and the worker restores the state it
# froze before it, which is no rollback: the skip must still apply. The
# document decides, so a compile that names a worker id still checks.
extra=(-async-proofs on -async-proofs-j 1)
skips async_bad "$bad" 'Qed.'
# The stm runs some commands under a resilience that drops their error, so the
# error of a check a rollback ran is raised again before the document ends.
# Without the skip this file stops at End S, with "Open proofs remain", so
# only the status is the same in every arm.
same_status resilient_reset_bad 1 'Section S.' 'Variable n : nat.' "$bad" 'Qed.' \
  'Reset discarded_bad.' 'Definition x := 0.' 'End S.'
says resilient_reset_bad "$kernel_error" option set inline
extra=(-worker-id qed_rollback)
rolls_back worker_id_reset_bad "$bad" 'Qed.' 'Reset discarded_bad.'

# (k) -vok writes no library, so nothing it processes reaches rocqchk and its
# exit status is the whole verdict: it typechecks every Qed proof. The option
# is refused with it, and the flag is forced off for the whole document, the
# files it loads first included, so no arm compiles an ill-typed proof, with
# the proof delegated to a worker or not.
extra=(-vok)
same_status vok_bad 1 "$bad" 'Qed.'
says vok_bad "$kernel_error" plain set inline
says vok_bad 'cannot be used with -skip-qed-typecheck' option
extra=(-vok -async-proofs on -async-proofs-j 1)
same_status vok_async_bad 1 "$bad" 'Qed.'
says vok_async_bad 'cannot be used with -skip-qed-typecheck' option
# -l loads its file before the first line of the case, so the arm that sets
# the flag there reaches it with the skip off: only the -set arm would skip.
extra=(-vok -l "$workdir/loaded_bad.v")
same_status vok_load_bad 1 'Definition after_load := 0.'
says vok_load_bad "$kernel_error" plain set
says vok_load_bad 'cannot be used with -skip-qed-typecheck' option
extra=()
