# Speed experiments

A log of the experiments of step 8, "Speed": what was tried, why, and what it did to a run over the corpus. The goal is a run that takes a quarter of the time or less.

## How a run is measured

- **The run.** `make benchmark`, which checks the 17,001 cases of corpus 0.8.0 one after the other, in both directions: 34,002 checks. The time is the wall-clock time of the whole run, and "in the checks" is the sum of the times of the checks, which leaves out reading the cases, validating the counterexamples and writing the results.
- **The machine.** An Apple M3 Pro with 11 cores. Other programs were at work on it during the runs, among them a virtual machine that used four to five cores, so a time is good to a few percent and no better. The load before each run is in `timings.csv`.
- **Verdicts first.** An experiment is kept only if no check loses its verdict, none is wrong and no counterexample is refused by the validator. That is seen with `make benchmark JOBS=8`, whose times are no more than a hint. The time of an experiment is then measured with one job.
- **The tests.** `cargo test --workspace` passes for every experiment that is kept.
- **`timings.csv`** has one line for each timed run.

## Where the time goes

The baseline is `9e48b0d`, release 0.4.0.

| | checks | time in the checks |
| --- | ---: | ---: |
| end at the budget of 10 million steps | 274 | 337 s |
| every other check | 33,728 | 40 s |
| the whole run | 34,002 | 377 s |

- 274 checks, 0.8% of all, take 89% of the time. Each spends the whole budget, which takes 1.2 s to 2.3 s, and ends in `Unknown`.
- They are of 62 schemas, most of them in two collections: a real schema against itself with `additionalProperties` written as `unevaluatedProperties`, and with `oneOf` written as `anyOf`.
- So a faster step is not what a quarter of the time takes: at 20 ns a step, a sixth of what it is, the 274 checks alone would still take 55 s. The checks have to be decided, or given up, in far fewer steps.

### What such a check does

`additional-as-uneval/o81108` is a schema of 3 kB: a `oneOf` of seven kinds of object that refer back to the `oneOf` in their items. A and B say the same in different words, so the check has to refute `B and not A`.

- A branch of it holds some fifteen disjunctions at once: the negation of each other alternative of the `oneOf` of B, and the negation of each alternative of the `oneOf` of A. Each is the negation of a conjunction, so it has five to eight alternatives.
- One of these disjunctions has no alternative that stands: the negation of the alternative of A that says what the chosen alternative of B says. Every one of its alternatives is refuted as soon as it is taken in.
- The branch splits its disjunctions in the order in which it met them, and that one comes late. So it is refuted anew under every combination of alternatives of the disjunctions before it, which have nothing to do with it. A trace of the check has 745,578 alternatives, of which 557,806 are refuted at once, in 187,751 splits, 19 deep.

This is thrashing, as constraint solvers call it, and the remedies are theirs: split first on the disjunction that is most likely to fail.

## Experiments

### E0. Baseline

`9e48b0d`. Three runs: 423 s, 382 s and 390 s for the whole run, 377 s to 418 s in the checks. The first run began with the machine under the most load.

23,597 `Yes`, 8,719 `No`, 1,686 `Unknown`, of which 274 at the budget. 3,096 million steps.

### E1. Split first on the disjunction that most often left no alternative

**Hypothesis.** The checks that end at the budget thrash: a disjunction all of whose alternatives are refuted at once is split last, under every combination of the others. If a branch splits first on a disjunction that has done so before, the work is the sum of the alternatives and not their product.

**Change.** The engine counts, for each disjunction, how often every alternative of a split on it was refuted before it came to a split of its own. A branch splits on the disjunction with the highest count, and on the one that it met first where none has a count, as before. This is the "last conflict" rule of constraint solvers, with a count in place of the last one. 60 lines in `normalize.rs`, and nothing is looked at ahead of a split, so a check that never backtracks does what it did.

**Result.** 194 checks that ended at the budget are decided: 180 `Yes` and 14 `No`. None is lost and none is wrong. 80 checks still end at the budget.

| | baseline | E1 |
| --- | ---: | ---: |
| `Yes` | 23,597 | 23,777 |
| `No` | 8,719 | 8,733 |
| `Unknown` | 1,686 | 1,492 |
| at the budget | 274 | 80 |
| steps | 3,096 million | 1,173 million |
