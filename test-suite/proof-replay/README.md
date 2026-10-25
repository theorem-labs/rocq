# Per-proof replay fixtures (BET-84 gate part 2)

`run.sh` compiles each fixture twice and compares the two compiles.  It answers
one question per fixture: **after this edit, does a replay compile give the same
result as a stock compile, and does it replay exactly the proofs it should?**

```sh
run.sh --list                       # name every fixture
run.sh BINDIR OUTDIR                # run them all except the slow one
run.sh --only hint_added BINDIR OUT # one fixture
run.sh --slow BINDIR OUTDIR         # add the budget fixture (minutes)
run.sh --register-only BINDIR OUT   # only the registration half (recorder Rocq)
```

`BINDIR` holds `rocq` and `rocqchk`.  A Rocq built with dune needs `ROCQLIB`,
`ROCQRUNTIMELIB` and `OCAMLPATH`; export them before the call, the runner passes
the environment through.  Nothing but `python3` is needed.  Rocq builds are not
allowed on sami-rocqperf: run this on speed-r1, under
`scripts/speed_loop/lanes/box/untimed.sh`.

## What one fixture is

```
fixtures/<name>/original/*.v   the tree that gets registered
fixtures/<name>/edited/*.v     the tree that gets graded
fixtures/<name>/expect.json    what must happen
```

The runner, per fixture:

1. compiles `original/` with `-proof-record` (the registration) and publishes
   the records under the names `-proof-replay-dir` reads;
2. checks `expect.json`'s `records` block against the registration's records;
3. compiles `edited/` in the tree `a/` with
   `-proof-replay-dir <records> -proof-replay-ratio <r>` and checks each
   `<base>.proof-replay.json` against `summaries`;
4. compiles `edited/` again in `b/` with no replay option, and requires the
   same exit code per file and the same `.vo` per file;
5. runs `rocqchk` over the replay run's objects.

`a/` and `b/` have one-character names because an object's `vmlibrary` bytes
depend on the length of the build path.

The `.vo` comparison follows lane R1's rule
(`scripts/speed_loop/lanes/r1/segcmp_norm.ml` in binary-equivalence-taiga): the
`vmlibrary` segment by value, every other segment by bytes.  Pass `--segcmp
PATH` (or `SEGCMP_NORM`) to use that program, which is the rule itself.  Without
it the runner compares segments in Python by the MD5 the segment table records;
it then cannot decide a `vmlibrary`-only difference and reports
`vmlibrary_bytes`, which fails the fixture.  Each line says which comparison ran.

## expect.json

| Key | Meaning |
|---|---|
| `doc` | one line, printed by `--list` |
| `files` | the `.v` files, in compile order; both trees use this list |
| `root` | the logical root of `-Q . <root>` (default `PR`) |
| `mode` | `replay` (default), `usage`, or `budget` |
| `slow` | run only with `--slow` |
| `requires` | prerequisites to probe first (`native`, `csdp`); a missing one skips |
| `native_compiler` | the `-native-compiler` value (default `no`) |
| `common_flags` | flags for every compile, registration included |
| `register_flags` | flags for the registration only |
| `grade_flags` | flags for both grade compiles (for example `-skip-qed-typecheck`) |
| `replay_extra_flags` | flags for the replay compile only |
| `ratio` | the `-proof-replay-ratio` value (default `1`) |
| `stack_kb` | run every compile of this fixture under that stack limit |
| `record_layout` | `dotted`, `slashed` or `both`: which name the record is published under |
| `records` | per file, per proof: `ineligible` reasons it must carry, `eligible`, `writes_nonempty`, `stores_no_term` |
| `summaries` | per file: `proofs`, `hits`, `misses`, `refused`, `killed`, `outcomes` |
| `compile_fails` | files whose compile must fail in both runs; no later file is compiled |
| `compare_stdout`, `compare_stderr` | files whose output must be identical in the two runs |
| `stdout_contains`, `stderr_contains` | substrings the replay run must print |
| `vo_exempt` | file -> reason: a `.vo` difference that the fixture allows |
| `coqchk` | run `rocqchk` over the replay objects (default true) |
| `budget`, `replay_wall_max` | the budget mode's seconds |
| `usage` | the usage mode's expected exit code and message substrings |

`outcomes` is a list of `[name, outcome]`, or `[name, outcome, channel]` for a
`read` miss.  It is checked only when the summary carries the field.

## The fixtures

**Both directions.**  `hint_added`, `hint_removed`, `const_added`,
`const_changed`, `const_deleted`, `opaque_added`, `opaque_removed`.

**Grain.**  `grain_lookup_hit` (an unused constant changes: per-lookup tracking
must HIT), `grain_hint_table` (an unused entry of a searched hint database
changes: the whole-database digest MISSES, and that is the expected result for
that grain).

**Place.**  `place_same_file`, `place_earlier_cone` (the change is in a file the
proof's file requires; the proof that read the changed constant misses, the
other hits).

**The verdict changes.**  `verdict_script_fails` (the stock script now fails, so
the replay compile must fail too), `verdict_assumptions` (`Print Assumptions` of
a later lemma must print the same list in both runs).

**Each replayed write**, each with a later proof in the same file that reads what
the earlier proof wrote: `write_universes`, `write_constraint_sources`,
`write_scheme_rewrite`, `write_unchecked_mark`, `write_counters`,
`write_warning`, `write_warning_as_error` (with `Set Warnings "+..."`, so the
warning fails the compile in both runs).

`write_scheme_rewrite` uses `rewrite` with a user equality, not `induction` or
`inversion`.  Measured on speed-r1 with the recorder at `d97df04b`: with
`Unset Elimination Schemes`, `induction` fails with "Cannot find the elimination
combinator bit_ind" instead of creating a scheme, and `inversion` on the same
inductive creates none (`writes.schemes` empty), while `rewrite` with a user
equality creates `internal_myeq_rew_r` and raises `missing-scheme`.

**Each ineligible class the recorder knows** (`lib/proof_recorder.mli`, and the
call sites of `Proof_recorder.ineligible`): `ineligible_timeout`,
`ineligible_external_prover`, `ineligible_native_compute`,
`ineligible_command`, `ineligible_subproof`, `ineligible_nested_proof`,
`ineligible_dependent_start`, `ineligible_message_to_string`,
`ineligible_catchall`, `ineligible_unhashable`.  The reason `read_changed` has
no fixture: it was removed from the recorder in commit `d97df04b` ("a repeat now
computes nothing ... The read_changed reason is gone with it").

`ineligible_catchall` and `ineligible_unhashable` carry `trigger_optional`.  No
source-level trigger for those two reasons is known on this Rocq; each
`expect.json` lists what was measured and found not to fire.  When the reason is
absent from the record, the runner prints SKIP with that text, so an untested
class is named on every run instead of passing silently.

**The closer.**  `closer_admitted`: a registered `tac. Qed.` against an edited
`tac. Admitted.` must miss.

**The options.**  `usage_no_ratio`: `-proof-replay` with no
`-proof-replay-ratio` exits 1, names the ratio and writes no `.vo`.

**The budget.**  `budget_kill` (`--slow`): one file of three slow proofs under
`-proof-replay-budget 240 -proof-replay-ratio 1`.  Stock is killed by its own
240-second `timeout`.  Replay charges two replayed proofs, runs the third, and
its charged clock reaches the budget, so it exits 124 with no `.vo` well before
240 seconds of real time.
