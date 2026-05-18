# Defer Sort Quality Collapse Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Let omitted sort qualities constrained only by `Prop <= ?q` remain unresolved during the `only_above_prop` minimization path, so later conversion can resolve them to `Prop` when needed.

**Architecture:** Add one focused regression test for the `bar1 = bar2` scenario, then change `QState.collapse` so above-Prop quality variables are not defaulted to `Type` when collapse is running in `only_above_prop` mode and no dominating quality forces `Prop`. Keep explicit, rigid, and non-`only_above_prop` collapse behavior unchanged.

**Tech Stack:** Rocq OCaml kernel/engine code, Rocq `.v` test-suite success tests, Dune build, test-suite Makefile.

---

## File Structure

- Create `test-suite/success/defer_sort_quality_collapse.v`: minimal regression test for ordinary omitted quality elaboration staying unresolved long enough for equality conversion to choose `Prop`.
- Modify `engine/uState.ml`: update the `QState.collapse` above-Prop branch only.
- No generated output files are intentionally changed by the implementation. Output tests are run as verification, not edited.

---

### Task 1: Add the Failing Regression Test

**Files:**
- Create: `test-suite/success/defer_sort_quality_collapse.v`

- [ ] **Step 1: Create the regression test file**

Create `test-suite/success/defer_sort_quality_collapse.v` with exactly:

```coq
Set Universe Polymorphism.
Set Primitive Projections.
Set Polymorphic Inductive Cumulativity.
Unset Collapse Sorts ToType.

Record bar {A} (a : A) : Prop := { }.

Definition bar1 : bar I := ltac:(constructor).
Definition bar2 : bar@{Prop;Set} I := ltac:(constructor).

Set Printing All.
Set Printing Universes.

Check eq_refl : bar1 = bar2.
```

- [ ] **Step 2: Run the new test and verify it fails before the fix**

Run:

```bash
make -C test-suite success/defer_sort_quality_collapse.v.log
```

Expected before the fix: the target fails. The log contains the universe inconsistency:

```text
The term "bar2" has type "@bar@{Prop ; Set} True I"
while it is expected to have type "@bar@{Type ; Set} True I"
```

- [ ] **Step 3: Commit the failing test**

Run:

```bash
git add test-suite/success/defer_sort_quality_collapse.v
git commit -m "test: cover deferred sort quality collapse"
```

Expected: one commit containing only the new `.v` test.

---

### Task 2: Defer Above-Prop Collapse in `only_above_prop` Mode

**Files:**
- Modify: `engine/uState.ml`

- [ ] **Step 1: Update the collapse decision**

In `engine/uState.ml`, find this branch inside `QState.collapse`:

```ocaml
        else if QSet.mem q m.above_prop then
          if QSet.exists (fun q' -> dominates_above_prop q' q) free_qualities then
            Option.get (set q qprop m)
          else Option.get (set q qtype m)
        else if not only_above_prop then Option.get (set q qtype m) else m)
```

Replace it with:

```ocaml
        else if QSet.mem q m.above_prop then
          if QSet.exists (fun q' -> dominates_above_prop q' q) free_qualities then
            Option.get (set q qprop m)
          else if only_above_prop then m
          else Option.get (set q qtype m)
        else if not only_above_prop then Option.get (set q qtype m) else m)
```

This preserves the existing `Prop` choice when a dominating quality exists. It also preserves eager `Type` collapse when `only_above_prop=false`. The only changed case is an above-Prop quality with no dominating quality during `only_above_prop=true`, which now remains unresolved.

- [ ] **Step 2: Build the Rocq binary**

Run:

```bash
OPAMROOT=/home/kanghee/.opam-local opam exec --switch=rocq-dev-coqhott-univp -- make world
```

Expected: the build succeeds and updates `_build/install/default/bin/rocq`.

- [ ] **Step 3: Run the new regression and verify it passes**

Run:

```bash
make -C test-suite -B success/defer_sort_quality_collapse.v.log
```

Expected after the fix: the target succeeds.

- [ ] **Step 4: Inspect the regression log for the key check**

Run:

```bash
sed -n '1,120p' test-suite/logs/success/defer_sort_quality_collapse.v.log
```

Expected: the log contains a successful `eq_refl` check and does not contain `universe inconsistency`.

- [ ] **Step 5: Commit the implementation**

Run:

```bash
git add engine/uState.ml
git commit -m "fix: defer above-prop sort quality collapse"
```

Expected: one commit containing only `engine/uState.ml`.

---

### Task 3: Run Focused Sort-Polymorphism Verification

**Files:**
- Test: `test-suite/success/sort_poly.v`
- Test: `test-suite/success/sort_poly_elim_csts.v`
- Test: `test-suite/success/sort_poly_elim_rigid_paths.v`
- Test: `test-suite/output/sort_poly_elab.v`
- Test: `test-suite/output/sort_poly_elim_error.v`

- [ ] **Step 1: Run nearby success tests**

Run:

```bash
make -C test-suite -B \
  success/sort_poly.v.log \
  success/sort_poly_elim_csts.v.log \
  success/sort_poly_elim_rigid_paths.v.log
```

Expected: all three targets succeed.

- [ ] **Step 2: Run output tests that exercise sort-quality elaboration**

Run:

```bash
make -C test-suite -B \
  output/sort_poly_elab.v.log \
  output/sort_poly_elim_error.v.log
```

Expected: both targets succeed. If `output/sort_poly_elab.v.log` fails only because printed universe names or quality output changed, inspect `test-suite/output/sort_poly_elab.out.real` before deciding whether the behavior change is acceptable.

- [ ] **Step 3: Run the test-suite summary for the focused targets**

Run:

```bash
make -C test-suite summary
```

Expected: the summary reports no failures for:

```text
success/defer_sort_quality_collapse.v
success/sort_poly.v
success/sort_poly_elim_csts.v
success/sort_poly_elim_rigid_paths.v
output/sort_poly_elab.v
output/sort_poly_elim_error.v
```

---

### Task 4: Verify the External Iso-Checker Regression

**Files:**
- Test: `/home/kanghee/autoformalization/iso-checker/Tests/CurrentExpectedFailure/RegressionPropElaboration/Interface.v`

- [ ] **Step 1: Compile a copied minimal external regression with the local Rocq build**

Run:

```bash
cp /home/kanghee/autoformalization/iso-checker/Tests/CurrentExpectedFailure/RegressionPropElaboration/Interface.v /tmp/RegressionPropElaboration_Interface.v
./_build/install/default/bin/coqc -q /tmp/RegressionPropElaboration_Interface.v
```

Expected: `coqc` exits successfully.

- [ ] **Step 2: Run the iso-checker focused log target when its makefile is compatible with the local compiler**

Run:

```bash
cd /home/kanghee/autoformalization/iso-checker
test -f .Makefile.coq.d && touch .Makefile.coq.d
OPAMROOT=/home/kanghee/.opam-local opam exec --switch=rocq-9.2 -- make Tests/CurrentExpectedFailure/RegressionPropElaboration/Interface.v.log
```

Expected with the opam Rocq 9.2 switch: this may still fail if that switch does not contain the local compiler change. Record the result. The authoritative verification for this branch is Step 1 with `_build/install/default/bin/coqc`.

---

### Task 5: Final Review and Cleanup

**Files:**
- Inspect: `engine/uState.ml`
- Inspect: `test-suite/success/defer_sort_quality_collapse.v`

- [ ] **Step 1: Check the final diff**

Run:

```bash
git diff HEAD~2..HEAD -- engine/uState.ml test-suite/success/defer_sort_quality_collapse.v
```

Expected: the diff contains only the new test and the single `QState.collapse` branch change.

- [ ] **Step 2: Check repository status**

Run:

```bash
git status --short
```

Expected: no unrelated source files are modified. Build artifacts and test logs should not be staged.

- [ ] **Step 3: Record verification commands in the final response**

Include these verification results:

```text
OPAMROOT=/home/kanghee/.opam-local opam exec --switch=rocq-dev-coqhott-univp -- make world
make -C test-suite -B success/defer_sort_quality_collapse.v.log
make -C test-suite -B success/sort_poly.v.log success/sort_poly_elim_csts.v.log success/sort_poly_elim_rigid_paths.v.log
make -C test-suite -B output/sort_poly_elab.v.log output/sort_poly_elim_error.v.log
./_build/install/default/bin/coqc -q /tmp/RegressionPropElaboration_Interface.v
```

If any command fails, include the exact failing target and the relevant diagnostic lines.

---

## Self-Review

- Spec coverage: the plan implements the approved option 1 by changing only the `only_above_prop` collapse behavior, adds the `bar1 = bar2` regression, and verifies nearby sort-polymorphism behavior.
- Placeholder scan: no placeholder markers or undefined follow-up actions are left in the task steps.
- Type consistency: the plan consistently names the new test `defer_sort_quality_collapse.v`, the implementation function `QState.collapse`, and the changed case as above-Prop plus `only_above_prop=true`.
