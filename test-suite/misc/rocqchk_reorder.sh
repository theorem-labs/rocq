#!/usr/bin/env bash
# With workers, when every library to check is named with -norec, rocqchk
# checks each library as soon as the libraries it depends on are read, and
# its workers start while later libraries are still being read. This checks
# that this changes nothing a reader can see when libraries are read in any
# order:
#
#  (a) B and C depend on A, and C on B; every opaque proof of B and C needs
#      A's or B's declarations. rocqchk reads the -norec names from the last
#      to the first, so the six orders of A, B and C read a dependency both
#      before and after the libraries that need it, as a root of its own or
#      inside their reading; two more orders leave A unnamed, so it is only
#      read as a dependency. Each order, and each with an ill-typed proof in
#      C, must print and end exactly as the run that reads every library
#      first (forced by -admit of a library that is admitted anyway).
#  (b) A library is refused when it is read (its name is not an identifier)
#      AFTER workers have started on libraries read before it, one of which
#      holds an ill-typed proof. The refusal wins, as it does when every
#      library is read first: same exit code, same output, and no type
#      error is reported.
#
# ROCQCHK_WORKER_WINDOW=0 deals the checks of a library as soon as it is
# checked, so that a library of a few hundred proofs forks a worker before
# the next library is read, whatever the speed of the machine. In (b) the
# test also sees it: ROCQCHK_OPAQUE_AT=before:B:dir makes the process that
# reads B's table create dir/before-PID, and only a worker reads it (the
# main process reads no table when it has workers, and the worker that
# reads every table starts only once every library is read, which a refused
# library never is).
set -eu
export PATH="$BIN:$PATH"
export ROCQCHK_WORKER_WINDOW=0
unset ROCQCHK_OPAQUE_AT

VO=misc/vo_segments.py
RENAME=misc/rocqchk_names/rename.ml
d=$(mktemp -d)
mkdir "$d/src" "$d/good" "$d/bad"
N=300

lemmas() {  # lemmas PREFIX TYPE PROOF: N lemmas PREFIXi : TYPE := PROOF, with i for {i}
  for i in $(seq 1 $N); do
    echo "Lemma $1$i : ${2//\{i\}/$i}. Proof. exact (${3//\{i\}/$i}). Qed."
  done
}
lemmas a True I > "$d/src/A.v"
{ echo "Require Import A."; lemmas b 'True /\ True' 'conj a{i} a{i}'; } > "$d/src/B.v"
{ echo "Require Import A B."; lemmas c '(True /\ True) /\ True' 'conj b{i} a{i}'; } > "$d/src/C.v"
# The ill-typed C: c7 proves another statement, so its opaque proof, put in
# the good C below, does not have the type the good C declares.
{ echo "Require Import A B."
  for i in $(seq 1 $N); do
    if [ "$i" = 7 ]; then
      echo "Lemma c7 : forall x : True, (True /\\ True) /\\ True. Proof. exact (fun x => conj b7 a7). Qed."
    else
      echo "Lemma c$i : (True /\\ True) /\\ True. Proof. exact (conj b$i a$i). Qed."
    fi
  done
} > "$d/bad/C.v"
( cd "$d/src" && for v in A B C; do rocq c -native-compiler no -R . "" "$v.v"; done )
cp "$d/src/A.vo" "$d/src/B.vo" "$d/bad/"
( cd "$d/bad" && rocq c -native-compiler no -R . "" C.v )
cp "$d/src/A.vo" "$d/src/B.vo" "$d/src/C.vo" "$d/good/"
# The ill-typed C: the good library segment, with the opaques of the C whose
# c7 has another type.
python3 "$VO" splice-opaques "$d/src/C.vo" "$d/bad/C.vo" "$d/bad/C.vo.spliced"
mv "$d/bad/C.vo.spliced" "$d/bad/C.vo"

leaf=Corelib.Init.Notations
fail=0
# same <label> <dir> <want: ok|refused> <rocqchk arguments...>: the run that
# checks while reading against the run that reads everything first.
same() {
  local label="$1" dir="$2" want="$3"; shift 3
  local r1=0 r2=0
  rocqchk -j 4 -R "$dir" "" "$@" > "$d/s.out" 2> "$d/s.err" || r1=$?
  rocqchk -j 4 -R "$dir" "" "$@" -admit "$leaf" > "$d/f.out" 2> "$d/f.err" || r2=$?
  if [ "$want" = ok ]; then
    if [ "$r1" = 0 ] && [ "$r2" = 0 ] && cmp -s "$d/s.out" "$d/f.out" && cmp -s "$d/s.err" "$d/f.err"; then
      echo "$label: same (exit code 0)"
    else
      echo "$label: differs (exit codes $r1 and $r2)"; diff "$d/f.err" "$d/s.err" | head -20 || true; fail=1
    fi
  else
    # Which worker held the proof, and its pid, depend on timing either way.
    for f in s f; do
      grep -h -E 'Fatal Error|Error:|Type error|while checking the opaque proof|not an identifier' \
        "$d/$f.out" "$d/$f.err" | sed -e 's/Worker process [0-9]*/Worker process PID/' | sort -u > "$d/$f.cmp"
    done
    if [ "$r1" != 0 ] && [ "$r1" = "$r2" ] && cmp -s "$d/s.cmp" "$d/f.cmp"; then
      echo "$label: same (exit code $r1)"
    else
      echo "$label: differs (exit codes $r1 and $r2)"; diff "$d/f.cmp" "$d/s.cmp" | head -20 || true; fail=1
    fi
  fi
}

# (a)
for order in "A B C" "A C B" "B A C" "B C A" "C A B" "C B A" "B C" "C B"; do
  args=(); for x in $order; do args+=(-norec "$x"); done
  same "(a) read order reversed from: $order" "$d/good" ok "${args[@]}"
  same "(a) ill-typed C.c7, read order reversed from: $order" "$d/bad" refused "${args[@]}"
  grep -q 'while checking the opaque proof of C.c7\.' "$d/s.cmp" ||
    { echo "(a) $order: expected the proof of C.c7 to be reported"; fail=1; }
done

# (b) X needs Forged, an admitted library whose label zqxlbl becomes a name
# with a line break; B is read first and holds the ill-typed c7 of (a).
mkdir "$d/b"
cp "$d/bad/A.vo" "$d/bad/B.vo" "$d/b/"
echo "Lemma zqxlbl : True. Proof. exact I. Qed." > "$d/b/Forged.v"
echo "Require Import Forged." > "$d/b/X.v"
( cd "$d/b" && rocq c -native-compiler no -R . "" Forged.v && rocq c -native-compiler no -R . "" X.v )
ocaml "$RENAME" "$d/b/Forged.vo" library zqxlbl $'zqx\nbl'
# C, renamed: the bad C read first is the library whose workers start early.
cp "$d/bad/C.vo" "$d/b/C.vo"
m=$d/marks; mkdir "$m"; touch "$m/go"
seen=0
for try in 1 2 3; do
  rm -f "$m"/before-*
  # Read order: C (and A and B inside its reading), then X, which reads Forged.
  ROCQCHK_OPAQUE_AT="before:C:$m" \
    same "(b) refused name read after early workers, try $try" "$d/b" refused -norec X -norec C
  grep -q 'not an identifier' "$d/s.cmp" ||
    { echo "(b) expected the name to be refused"; fail=1; }
  if grep -q -E 'Type error|while checking the opaque proof' "$d/s.cmp"; then
    echo "(b) the ill-typed proof was reported, not the refused name"; fail=1
  fi
  ls "$m"/before-* > /dev/null 2>&1 && seen=$((seen + 1))
done
echo "(b) a worker read C's table before the refusal in $seen of 3 tries"
[ "$seen" -gt 0 ] || { echo "(b) no worker started before the refusal: nothing was tested"; fail=1; }

exit $fail
