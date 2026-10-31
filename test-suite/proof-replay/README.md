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
| `alt_register_flags` | register again with these flags, replay from that record in `c/`, and require the same exit codes, hits and `.vo` bytes as from the first record |
| `vo_mutation` | `remove` or `change` the registered `.vo` published beside each record (one byte of its opaque proofs) |
| `record_trailers` | per file: `vo_opaques` true or false, whether the record refers to its `.vo` |

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
`write_scheme_rewrite`, `write_unchecked_mark`, `write_counters`.  A warning is
not a replayed write: a proof that raises one is ineligible (reason `warning`),
so `write_warning` expects its writer `ineligible`, and `write_warning_as_error`
(with `Set Warnings "+..."` in the edited tree) fails the compile in both runs
because the writer runs.

`write_scheme_rewrite` uses `rewrite` with a user equality, not `induction` or
`inversion`.  Measured on speed-r1 with the recorder at `d97df04b`: with
`Unset Elimination Schemes`, `induction` fails with "Cannot find the elimination
combinator bit_ind" instead of creating a scheme, and `inversion` on the same
inductive creates none (`writes.schemes` empty), while `rewrite` with a user
equality creates `internal_myeq_rew_r` and raises `missing-scheme`, which the
fixture disables so that its proofs stay eligible.

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
evaluator has no hit test: a proof asks those hooks only when a
`canonical_structure` lookup finds no solution, which no fixture's
replayed proof does.

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
a key back, so `same` missed with why `unknown`.  `eval_canonical_structure`:
the canonical instances of a projection, which one more `Canonical` changes.

**Ltac definitions by value.**  A definition is read without its source
locations.  `ltac_redef_moved` and `ltac_alias_moved`: an `Ltac ... ::=`
redefinition and a `Tactic Notation` move to another line with the same
body, and the proof that uses them replays; `ltac_redef_changed` and
`ltac_alias_changed`: their bodies change, and the proof misses on
`tactic_definition` and `tactic_alias`.

**The cross-model soundness review of `5f39c90b`.**  Each fixture is a
reviewer's scenario; stock and replay must agree.
`universe_checked_proof_unchecked_graph`: the global graph does not check
universes, a proof checks its own, and a constraint it needs is reversed;
stock rejects the proof.  `vm_inline_lib`, `vm_inline_same_file`: a changed
constant is inlined (`Register Inline`) into the bytecode of an unchanged one
that a proof runs with `vm_compute`; stock rejects the proof.
`vm_global_unchanged_hit` is their control: unchanged bytecode, moved in the
library's code table, still replays.  `vm_lia_hit`: two `lia` proofs, whose
certificate check runs the machine over Stdlib's checker, replay on a cold
and on a warm cache; its replay `.vo` differs from stock's only in the
sharing of the string "BinInt" (`EXEMPTIBLE_FIXTURES` in `runner.py`).
`vm_cache_lib`, `vm_cache_same_file`:
an `Eval vm_compute` fills the machine's cache with an unchanged constant
that calls a changed one, and a proof then runs it from the cache; stock
rejects the proof.  `prim_token_warning_threshold`: a number notation's
warning threshold drops below a number a proof reads, under `Set Warnings
"+large-number"`; the term and scope do not change, and stock rejects the
proof.  `warning_error_caught`: a `try` catches a warning raised as an error,
and stock accepts the proof; the proof is ineligible (`warning`), so
replay does not raise the warning again, and the control replays.

**The second soundness review, of `08e77b30`.**  `vm_named_fv`: a cached
machine value closes over a section `Let` whose body calls a changed
constant; stock rejects the proof.  `warning_attribute_enabled`: a proof
sentence's warnings attribute makes an error-level warning a plain one, and
stock accepts the proof; `warning_lazy_registration`: a proof creates a
warning the first time it needs it, and a later command names it.  Both
proofs are ineligible (`warning`, and `warning_registry` for the second), so
replay runs them as stock does.

**The third soundness review.**  `vm_named_fv_clearbody`: a proof clears a
section `Let`'s body, then takes from the machine's cache a value that
closes over that `Let`; stock rejects the proof, which is ineligible
(`vm_section_closure`).  `warning_registry_history`: an earlier
proof no longer creates a disabled warning that a proof found created, and
a later command names it; that proof misses on the `warnings_registry` read
it starts with, runs, and creates the warning as stock does.
`warning_registry_unchanged_hit` is its control: the same registry, and the
proofs replay.

**The fourth soundness review.**  `vm_section_closure_creator`: a proof
fills the slot of a constant that closes over a section `Let`, and a later
proof takes it from the cache after clearing the `Let`'s body; a replay of
the first would leave the slot empty, so every use of such a slot, filled
or cached, makes a proof ineligible (`vm_section_closure`), and
`vm_named_fv_cold_fill` shows it for a proof that fills the slot alone.
`vm_named_fv_reset`: `Reset` and a second declaration give a name another
code; what the first code reaches must not answer for the second, so that
answer is kept with the declaration, not the name.  `late_reset_congruence`:
`Reset` restores a Rocqlib registration but not the process-wide lazy a
proof before it forced; `Reset`, `Back` and `BackTo` are late commands, so
that proof runs, and replay accepts the later proof as stock does.

**The cross-model review of `777213df6e`.**  Two global inputs that no read
recorded.  `open_module_contents_assert`: a proof asks Ltac2 for the fields
of the module it is in, which is open, and asserts that there are none; the
edited tree declares a definition before it, and stock fails the
assertion.  `eval_open_module`: that query and Ltac2's `Module.is_functor`
and `Module.is_modtype` on an open module are reads on channel
`open_module`; the three answers the edited tree changes (a definition
before the proof, a functor that becomes a plain module, a module type
that becomes a plain module) miss on that read, and the answer it does not
change replays.  Its proofs call the queries through Ltac2 definitions made
before the first `Qed`, which the source scan needed before
`late_qualified_module_word` fixed it.
`retroknowledge_primitive_changed`: a proof types an int63 literal, whose
type the kernel takes from its registry of primitive types, and the edited
tree registers `p` as the float64 type instead of the int63 type; stock
cannot type the literal.  `eval_retroknowledge`: one more `Primitive`
between two such proofs; the later one misses on the start-of-proof read
`retroknowledge`, and the earlier one replays.  A third input of the same
kind, found while fixing these: `eval_objlabel`.  A proof's `rewrite` with a
user equality creates a scheme, which the proof term inlines, and the
scheme's binders are named away from the labels of the module being built
(`Safe_typing.exists_objlabel`), which the nametab does not show.  The
edited tree declares `HC` before the proof, so stock writes the binder
`HC0` where the stored term holds `HC` (vodiff of the opaques segment on
`777213df6e`: 1 value difference); the proof must miss on the `objlabel`
read.  It has no replaying proof: a replayed proof that carries a scheme
writes a library segment whose sharing differs from stock's, which only
`write_scheme_rewrite` may excuse, and that fixture's proofs read the same
names unchanged and replay.

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
`Reset`, `Back` and `BackTo` are late commands too: they restore the Rocqlib
table, not a lazy value a proof forced (`late_reset_congruence`).

A `Require` is late for a proof only while a library it names is not loaded
when the proof opens: one of loaded libraries loads nothing, so it applies no
`Register` and loads no plugin.  `refused_detail` then counts the `Require`s
after the last command that is late whatever is loaded.
`late_require_loaded_hit`: two such `Require`s (a library the file loaded,
and one the prelude loaded) after the first proof, and both proofs hit.
`late_require_transitive`: the file requires `PR.Top` before its first proof,
which loads `PR.Dep`; a later `Require Import PR.Dep` loads nothing, and the
proof before it hits.  `late_require_unloaded`, `late_require_plugin`,
`late_require_register`: a `Require` of a library not yet loaded (a plain
one, one that loads a plugin, one that carries a `Register`) keeps the proof
before it from replaying, and a second `Require` of it, after the next proof,
does not.  A `Require` that loads a library after a replayed proof all the
same stops the compile with an anomaly; the unit test
`proof-replay-require-tripwire` checks that.  No fixture adds a load path
between a proof and a `Require`: no command changes the load path since `Add
LoadPath` was removed (`doc/sphinx/changes.rst`, #17394).  `Add LoadPath "d"
as P.` is now a syntax error, and `Add LoadPath "d".` or `Remove LoadPath
"d".` is an option-table command that fails: there is no `LoadPath` table.

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

**The record format** (`-proof-record-no-graph`, `-proof-record-vo-ref`).
Measured on r484-final, 99.6% of a stored term's bytes were the global
universe graph its universe state carries, and 0.25% the proof term.
`rebuild_replay`: with `-proof-record-no-graph` the stored terms are a few
hundred bytes instead of about 64 kB (`replay_max_bytes`), both proofs replay
through a rebuilt graph, and to the same `.vo` as from a record that keeps the
graph (`alt_register_flags`).  `rebuild_graph_changed_hit`: the global graph
changes in a way the universe footprint allows, and the proof still replays.
`rebuild_state_differs`: a universe state of 130 levels is checked against the
digest of the whole global graph, and a constraint between two universes the
proof never queries makes it miss on `universe_rebuild`.  `voref_replay`: with
`-proof-record-vo-ref` the proof's term is an index into the registered
`.vo`'s opaque proofs and the proof replays through it.  `voref_same_vo`: five
proofs replay to the same `.vo` bytes from references as from inline terms.
`voref_inline_cases`: the registered `.vo` is missing (`vo_mutation:
remove`); the plain lemma and the two section lemmas refer to it and miss on
`vo_term`, the polymorphic lemma (its term names its level, the table holds
it abstracted) and the section `Let` (a section variable, with no table
entry) kept their terms inline and replay.  `voref_object_changed`: one byte of
the registered `.vo`'s opaque proofs changed (`vo_mutation: change`), and the
proof that refers to it misses on `vo_term`.  `late_qualified_module_word`:
`Module.module_contents` in a tactic is a qualified identifier, not a late
command, and every proof of the file replays.

**Gate review, INFRA-361 gap 2.**  `load_inner_proof`: a `Load`ed file's
sentences run inside the one `Load` sentence, so the toplevel keeps none of
them as a proof's sentences and decides no proof among them.  A proof that the
loaded file opens is ineligible (reason `load` in the record, outcome
`ineligible` on channel `load` in the summary) and leaves no candidate open.
Before, the candidate stayed open after the `Load`, and the toplevel kept the
sentences after it as that proof's: in `B.v` it kept a `Proof.` that has no
proof to act on and reported the syntax error of the next sentence, where
stock reports the `Proof.`.  In `A.v` the loaded file changes a constant: the
proof that unfolds it misses on that read, and a later proof replays.  A proof
after a `Load` needs no rule of its own: the loaded sentences reach it only
through the global state, which its reads compare, as for a command of the
file itself.

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

