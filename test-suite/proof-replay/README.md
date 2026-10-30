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
| `mode` | `replay` (default), `usage`, `budget`, or `mixed` |
| `slow` | run only with `--slow` |
| `requires` | prerequisites to probe first (`native`, `csdp`); a missing one skips |
| `native_compiler` | the `-native-compiler` value (default `no`) |
| `common_flags` | flags for every compile, registration included |
| `register_flags` | flags for the registration only |
| `grade_flags` | flags for both grade compiles (for example `-skip-qed-typecheck`) |
| `replay_extra_flags` | flags for the replay compile only |
| `ratio` | the `-proof-replay-ratio` value (default `1`) |
| `stack_kb` | the stack limit every compile of this fixture runs under (default 8192, the limit a grade runs under; lane R1 measured that this changes `.vo` bytes, so stock and replay must share it). `prlimit` is required |
| `record_layout` | `dotted`, `slashed` or `both`: which name the record is published under |
| `records` | per file, per proof: `ineligible` reasons it must carry, `eligible`, `writes_nonempty`, `stores_no_term` |
| `summaries` | per file: `proofs`, `hits`, `misses`, `refused`, `killed`, `fence`, `outcomes` |
| `compile_fails` | files whose compile must fail in both runs; no later file is compiled |
| `compare_stdout`, `compare_stderr` | files whose output must be identical in the two runs |
| `stdout_contains`, `stderr_contains` | substrings the replay run must print |
| `vo_exempt` | file -> reason: a `.vo` difference that the fixture allows |
| `coqchk` | run `rocqchk` over the replay objects (default true) |
| `budget`, `replay_wall_max` | the budget mode's seconds |
| `usage` | the usage mode's expected exit code and message substrings |
| `mixed` | the mixed mode's `replay_file`, `carry_files` and `check_files` |

`outcomes` is a list of `[name, outcome]`, or `[name, outcome, channel]` for a
`read` miss.  It is checked only when the summary carries the field.

## The fixtures

**Both directions.**  `hint_added`, `hint_removed`, `const_added`,
`const_changed`, `const_deleted`, `opaque_added`, `opaque_removed`.

**Grain.**  `grain_lookup_hit` (an unused constant changes: per-lookup tracking
must HIT), `grain_hint_table` (an unused entry of a searched hint database
changes: the whole-database digest MISSES, and that is the expected result for
that grain).

**Universe constraints.** `universe_constraint_unused` adds a constraint over
levels the proof never queries and must hit. `universe_constraint_changed`
changes the transitive constraint projection of levels the proof queries and
must miss on `universe_constraint`.

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

`ineligible_catchall` reaches the handler at `tactics/equality.ml:466`: a
`rewrite` on a user equality resolves the `Has_J` class over the hint database
`rewrite_instances` inside that handler, so a `Hint Extern` there that
overflows the stack is caught and marks the proof, and `rewrite` still closes
through its fallback.  `ineligible_unhashable` (`--slow`) is the one class
`digest_value` refuses that source can reach: a constant whose body has more
than 2^25 distinct blocks.  Both fixtures' `.v` files carry the measurement
and the control behind them, and `expect.json` still supports
`trigger_optional` for a class whose trigger is lost to a later change: the
runner then prints SKIP with that text instead of passing silently.

**The recorder's fix round** (`9.2/proof-replay` `a1210789cf..23b37e36fb`).
`channels_unchanged`: one proof per channel the round added or changed —
`keyword` (fresh's keyword test), `autorewrite` with the base found and with
it absent, `typeclass_solver`, `coercion_hooks` — and nothing they read
changes, so every proof must replay; a channel without an evaluator makes its
proof miss.  `keyword_added` (a `Reserved Notation` makes fresh's string a
keyword), `rewrite_base_created` (a base the registration found absent is
created) and `rewrite_hints_changed` (a hint of the base turns around, read
through `rewrite_strat`'s `hints` and through `autorewrite`) must miss on that
channel's read: in each, the stored term is not the term stock makes.
`ineligible_par`: `par:` runs its tactic in a worker process, so the proof is
ineligible and is not replayed though the tactic it ran changed.  The plugin
hooks and the process-wide fence need a plugin, so their test is
`test-suite/misc/proof-replay-plugin-hooks.sh`.  The `canonical_hooks`
evaluator has no hit test: a proof asks those hooks only after a
`canonical_structure` lookup, which replay does not evaluate yet, so such a
proof misses there before its hook read is checked.

**One fixture per evaluated channel**, named `eval_<channel>`.  Each has two
proofs.  `changed` makes a read whose value the edited tree changes, and must
miss on that read (why `changed`).  `same` makes the same kind of read on a
value that does not change, and must replay; before its channel had an
evaluator it missed with why `no_evaluator`.  `eval_notation`: the
interpretation of a notation.  `eval_zify_table`: the zify operator table,
which an `Add Zify` between the two proofs changes.  `eval_prim_token`: the
scope a number is read in.  `eval_ltac2_global`: the body of an Ltac2
definition.  `eval_reserved_type`: the reserved type (`Implicit Types`) of a
binder.  `eval_abbreviation`: what an abbreviation stands for.
`eval_delimiters_scope`: the scope a delimiting key names.
`eval_ltac2_notation`: what an Ltac2 notation expands to.
`eval_proof_using_set`: the set a `Proof using` sentence gives.  Its
`changed` proof misses on `named_context`, not on `proof_using_set`: the set
is computed from inputs the proof records before it (the section context,
the statement, the collections), so a set that changes is always caught
there first.  `eval_proof_using_collection`: the expression of a named
collection of section variables.  `eval_bidirectionality_hint`: the hint of
a variable, whose key is its name; before, the evaluator could not read such
a key back, so `same` missed with why `unknown`.

**The cross-model soundness review of `5f39c90b`.**  Each fixture is a
reviewer's scenario; stock and replay must agree.
`universe_checked_proof_unchecked_graph`: the global graph does not check
universes, a proof checks its own, and a constraint it needs is reversed;
stock rejects the proof.

A summary's `fence` is `null`, or `"<reason>: <detail>"` of the process-wide
fence (`Proof_recorder.fence_tripped`) that refused a proof of the file: once
one trips, no later proof of the process is replayed, and each is counted as
`ineligible`.

**Late commands.**  A command after the first closer that can rebind a
Rocqlib name or load code keeps every proof that opens before the last such
command from replaying (outcome `ineligible`, channel `rebind`, why
`before_late_command`); `refused_detail` names the first command, its line and
the last one's byte offset.  `rebind_after_hit`: the proofs before a late
`Register` run, and the rebinding trips the Rocqlib fence for the proof after
it.  `plugin_after_hit`: the proof before a late `Declare ML Module` runs, and
the proof after it misses on its key (the loaded plugins are in it).
`late_command_hit`: the same load in both trees, and the proof after it hits.

**The closer.**  `closer_admitted`: a registered `tac. Qed.` against an edited
`tac. Admitted.` must miss.

**The options.**  `usage_no_ratio`: `-proof-replay` with no
`-proof-replay-ratio` exits 1, names the ratio and writes no `.vo`.

**The budget.**  `budget_kill` (`--slow`): one file of three slow proofs under
`-proof-replay-budget 240 -proof-replay-ratio 1`.  Stock is killed by its own
240-second `timeout`.  Replay charges two replayed proofs, runs the third, and
its charged clock reaches the budget, so it exits 124 with no `.vo` well before
240 seconds of real time.  The three times have to separate — the charge of
the two replayed proofs, which carries the recorder's overhead, below the
budget, and the stock compile well above it — so the proof's work is
calibrated, and `replay_wall_max` is tight enough (70 s against a ~92 s proof)
that a kill which lands only between top-level sentences, instead of inside
the third proof's tactic, fails the fixture.

**The carry-over.**  `carry_replayed_dep` (`mixed` mode): a grade that reuses
one registered object and replays the object it was compiled against.  `B.vo`
is compiled against the STOCK `A.vo`, then placed beside the REPLAYED `A.vo`,
and `C.v` is compiled on top.  It must behave as the all-stock control does,
and `rocqchk` must accept the reused object.  The control runs first, so a
broken setup fails there instead of looking like a pass.

## Comparing a replayed `.vo` against stock: the contract, and two traps

The acceptance contract (GRADE, 2026-10-26) is **not** byte identity.  In its
words: "verdict identical; the tree loads; `coqchk` accepts every replayed
object; and every segment's content is value-equal to stock's, EXCLUDING
recorded dependency digests, whose differences must each be explained by a
difference in the object they name."  A recorded dependency digest is a
reference to another object's bytes, not content of its own.

That last clause is a **standing obligation**, not a one-off: every excluded
difference must be shown to be a 16-byte string equal to the library MD5 of
that same `.vo` on that side.  `vodiff_all.py` is the tool that does it, and a
sweep must cover every object, never a sample.

Two traps, both of which have already produced a wrong answer here:

1. **`segcmp_norm` cannot see this class at all.**  It normalises dependency
   digests away, so an object whose digests differ looks identical to it.  In
   the 2026-10-26 lane run it reported 41 differing objects out of 262; the
   real count was 262, of which 239 differed only in digests.  It must never be
   the only comparison.
2. **`vodiff.py` lists at most 20 differences per segment but counts them
   all.**  The cap is on the listing (`vodiff.py:252,254`); the count printed
   at `:257` is `len(out["diff"])`, uncapped.  Classifying from the listing
   gave two false "value differs" objects at 30 and 31 differences, both
   wholly dependency digests.  Judge on the count, or call `compare()` and walk
   `out["diff"]` yourself as `vodiff_all.py` does.

One further caveat on `vodiff.py` for anyone extending it: `compare()`
memoises on `(id(a), id(b))` and returns `True` on a revisited pair even when
that pair differed on its first visit, so its BOOLEAN result is unreliable on a
DAG.  The difference is still recorded in `out["diff"]`, so the count is
sound — which is why everything here judges on the count.

```sh
python3 vodiff.py REPLAY.vo STOCK.vo library       # one segment, counts + first 20
python3 vodiff_all.py REPLAY.vo STOCK.vo library   # every difference, digests resolved, JSON
```

