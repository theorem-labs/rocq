# Defer Sort Quality Collapse Design

## Context

The regression in
`/home/kanghee/autoformalization/iso-checker/Tests/CurrentExpectedFailure/RegressionPropElaboration/Interface.v`
fails because `bar1 : bar I` elaborates its omitted record quality as
`@bar@{Type;Set} True I`, while `bar2` explicitly uses
`@bar@{Prop;Set} True I`.

The bad choice is made before tactics run. Elaborating `bar I` creates a fresh
quality variable for the first universe component of `bar`. The argument
`I : True` supplies only cumulativity evidence, `Prop <= ?q`, so the variable is
marked as above Prop. Later universe minimization collapses that unresolved
above-Prop variable to `Type` when no dominating quality variable forces it to
`Prop`.

## Goal

Try the broader behavior: ordinary elaboration should prefer leaving omitted
sort qualities unresolved longer, so later conversion or equality constraints
can force the more precise sort. The concrete success case is that `bar1 = bar2`
checks without requiring an explicit universe instance on `bar1`.

## Non-Goals

- Do not special-case `bar`, empty records, `I`, or equality.
- Do not change the meaning of explicit universe instances such as
  `bar@{Prop;Set}`.
- Do not introduce a broad rewrite of universe minimization.
- Do not make unrelated changes to primitive-record elimination-checking work
  on the current branch.

## Approach

Adjust the quality-collapse path used by universe minimization so an unresolved
quality known only to be above Prop is not eagerly collapsed to `Type` in the
`only_above_prop` case. The intended effect is:

- If later constraints force `Prop`, the quality can still become `Prop`.
- If ordinary declaration finalization truly requires a concrete quality, the
  existing finalization or conversion checks should surface that requirement.
- Existing explicit and rigid qualities remain unchanged.

This starts as an experiment. If keeping above-Prop qualities unresolved causes
invalid declarations or widespread test failures, back out and reconsider a
narrower expected-type-only design.

## Data Flow

1. Pretyping an omitted polymorphic global instance creates fresh quality
   variables through `Evd.fresh_global`.
2. Cumulativity from `Prop` to the fresh quality records `Prop <= ?q` as
   above-Prop evidence.
3. Universe minimization calls quality collapse with `only_above_prop=true`
   when collapse-sort-variables is disabled.
4. The proposed change alters only step 3: keep the above-Prop variable open
   instead of defaulting it to `Type` when there is no dominating quality.
5. Later conversion for `bar1 = bar2` can then resolve the variable to `Prop`.

## Testing

Use a focused sequence:

1. Compile the reduced regression and confirm `Check eq_refl : bar1 = bar2`
   succeeds.
2. Run nearby universe/sort elaboration tests in the Rocq test suite.
3. If practical, run the relevant iso-checker log target for
   `Tests/CurrentExpectedFailure/RegressionPropElaboration/Interface.v`.

The experiment is acceptable only if the reduced regression passes and focused
Rocq tests do not reveal incompatible unresolved-quality fallout.
