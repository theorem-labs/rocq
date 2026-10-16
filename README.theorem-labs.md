# About this branch

This branch is Rocq 9.2 plus a small set of changes that are either
already in later upstream releases, proposed upstream and not yet merged,
or specific to this branch. It exists so that tools which need those
changes, in particular `Require (safe)`, can pin one documented,
reproducible revision.

Everything here is licensed as upstream Rocq is (LGPL-2.1-only). The
upstream project is <https://github.com/rocq-prover/rocq>, and its own
README is `README.md`.

## Base and version

- Base: upstream commit `e91ea0887cc5f457e87543e96e38431386a9870f` on the
  upstream `v9.2` branch. It comes after the `V9.2+rc2` tag and 22
  commits before the `V9.2.0` tag.
- This tree therefore reports version `9.2+rc2` and `vo_magic` `90199`.
  Its `.vo` files are not interchangeable with those of the `V9.2.0`
  release (`vo_magic` 90299) or of `V9.3.0` (`vo_magic` 90300).
- Opam packages built from this tree are conventionally pinned under the
  version label `9.2.0`. The label is just a pin name: the binaries still
  report `9.2+rc2`.

## Relationship to the previous history

The changes were first developed as 74 commits on top of the base: 71
changes and 3 merge commits. This branch regroups the same changes into
eleven topical commits. The tree of the eleventh commit is byte-identical
to the tree of the previous pinned revision, `b0adcb1504104884549a51972e6374601e84600e`
(tree `3574f897d55ed7d4c1eb1793c02e0c2daba5e26a`). The final commit adds
only this file. Building this branch produces exactly what the previous
revision produced.

Each commit message lists the original commits it regroups.

## What each commit adds

"In 9.3.0" means the change, or an equivalent upstream fix, is in the
upstream `V9.3.0` release. "Open" means the upstream pull request has not
been merged yet.

| # | Commit | Upstream status |
|---|--------|-----------------|
| 1 | Build with dune 3.21 and `(rocq.theory)`; add a `coq.opam` metapackage | dune part: rocq-prover/rocq#21660, in 9.3.0. `coq.opam`: specific to this branch |
| 2 | `rocq dep`: faster file maps and lexer use | #21765, #21771: in `V9.2.0` |
| 3 | Backport kernel and vernacular fixes from Rocq 9.3 | #21531, #21774, #21779, #21825, #22164: in 9.3.0. Earlier or alternative versions of #22221, #21952, #22061, which are in 9.3.0 |
| 4 | Ltac2: scheme lookup, `with_strategy`, and `in_context` helpers | #21658, #21881, #21762: in 9.3.0. `in_context` / `map_in_context` (#22060, #22062): closed upstream, not merged |
| 5 | Unification: recheck casts after evar inversion (two flags, off by default) | #21740: open |
| 6 | Kernel: cumulative sort-polymorphic inductives support `Prop <= Type` | #21773: closed upstream, not merged |
| 7 | Kernel: faster module subtyping and module substitution | #22281: closed upstream, not merged. Substitution deferral: specific to this branch |
| 8 | Printing: `Printing Sorts`, `Printing Reversible`, anonymous quality variables | #22155: open. #22283: merged for 9.4, not in 9.3.0. #22310: open |
| 9 | `Require (safe)` | #22291: open, milestone 9.4 |
| 10 | Report `check_eliminations` bypasses in `Print Assumptions` and `rocqchk` | #22294: open, milestone 9.4 |
| 11 | `rocqchk` validation fixes | #22361, #22363, #22353: in 9.3.0. This branch carries an earlier revision of #22353 |

All pull request numbers refer to <https://github.com/rocq-prover/rocq>.

### Why each change is here

1. **Build.** The dune changes match upstream's packaging. The `coq`
   metapackage means that, once this tree is pinned with opam, packages
   that depend on `coq` resolve to it rather than to an old Coq release.
2. **`rocq dep` performance.** These are upstream 9.2.0 fixes that
   postdate the base.
3. **Kernel and vernacular fixes.** These make universe level comparisons
   fail only under type-in-type, add the `check_eliminations` typing flag,
   track and report inductives that depend on indices not mattering, add
   `Set Indices Matter`, make `Print Assumptions` traverse definition
   types, add `Set Printing All Assumptions`, stop rewriting schemes from
   baking template universes in, give primitive eta to records with only
   irrelevant fields when elimination checks are disabled, and fix a
   `contract_case` anomaly on evar-backed branches.
4. **Ltac2 APIs** used by proof automation: scheme lookup by kind
   (including SProp case analysis), `with_strategy`, and helpers for
   working under binders.
5. **Evar inversion.** Universe constraints of `Cast` nodes produced by
   evar inversion were not checked (rocq-prover/rocq#21733). The fix is
   guarded by the flags `Unification Recheck Casts` and
   `Unification Full Retyping`, both off by default.
6. **Sort cumulativity** for cumulative sort-polymorphic inductives, plus
   two fixes: a bad sort quality variance is reported as an error rather
   than an anomaly, and the variance check allows delta unfolding.
   Upstream closed the original pull request without merging it.
7. **Module performance.** Chains of `<+` over functor module types took
   quadratic time (rocq-prover/rocq#22279). Module substitution
   composition is deferred, and `rocqchk` validates the persisted form.
8. **Printing** options for output that can be read back in: sort
   structure without internal level names, reversible printing that
   escalates printing options until the output reparses to an equal term,
   and `_` for unnamed sort quality variables.
9. **`Require (safe)`** loads a library and its dependencies with only
   their kernel-level content and fully qualified names. No plugins,
   notations, hints or flag settings are replayed, so loading a library
   cannot change the state the loading document runs in beyond adding
   that content. Safe-loading
   propagates to the dependencies of libraries compiled with it.
   `Import` and `Export` are supported.
10. **Assumption reporting.** Declarations whose sort elimination
    constraints were not checked are now reported, both by
    `Print Assumptions` and by `rocqchk`.
11. **`rocqchk`.** It accepts the string primitives in VM data
    validation, validates every library named on the command line
    regardless of argument order, and compiles VM bytecode itself instead
    of trusting the bytecode serialized in the `.vo` file.

## Building

You need OCaml 4.14 or later, findlib, zarith, and dune 3.21 or later.

### With opam

Pin the three packages to a local clone or to a revision of this branch,
then install:

```sh
for p in rocq-runtime rocq-core coq-core; do
  opam pin add --no-action "$p.9.2.0" "git+<repository-url>#<revision>"
done
opam install rocq-runtime.9.2.0 rocq-core.9.2.0 coq-core.9.2.0
```

Packages such as `rocq-stdlib` declare version constraints on these
packages, so installing them against this tree may need
`--ignore-constraints-on=coq,coq-core,rocq-core,rocq-runtime,rocq-stdlib`.

### From a checkout

```sh
./configure -release -relocatable -native-compiler no
make dunestrap
dune build -p rocq-runtime,rocq-core @install
```

The binaries are under `_build/install/default/bin`. See `INSTALL.md` for
the full upstream instructions, including the test suite.
