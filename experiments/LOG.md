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
| the whole run, one job | 382 s to 423 s | 130 s |

**Kept.** A run takes 34% of the time it took.

### E2. A disjunction inside a disjunction counts against the one that brought it

**Hypothesis.** After E1, a trace of `additional-as-uneval/o81108` shows the thrashing one level up. The negation of an alternative of A is the negation of a conjunction of two conjunctions, `not all[X, Y]`. Each of its two alternatives stands when it is taken in and brings a disjunction of its own, `not X` or `not Y`, and it is that one whose alternatives are all refuted. E1 counts the inner disjunction, which a branch has only met once it has split on the outer one. The outer one never has a count, so it is still split last: 17,862 times in one check.

**Change.** An alternative that stands, and then splits on a disjunction that it brought itself, does not count as standing if that split leaves it with no alternative. So a split on `not all[X, Y]` whose two alternatives both end that way is a dead end of `not all[X, Y]`, and the count goes up the nesting. A split notes whether its disjunction was brought by the alternative that led to it: whether it was not among the disjunctions that the split below had met.

**A variant that was dropped.** To split first on a disjunction that the alternative brought, where no disjunction has a count, so that a nest of negated conjunctions is always taken apart in one go. On one case of each of the 62 schemas it decides 15 checks fewer than the change above, 90 where that decides 105, and takes 376 million steps where that takes 233 million.

**Result.** 44 more checks are decided: 42 `Yes` and 2 `No`. None is lost and none is wrong. 36 checks still end at the budget.

| | baseline | E1 | E2 |
| --- | ---: | ---: | ---: |
| `Yes` | 23,597 | 23,777 | 23,819 |
| `No` | 8,719 | 8,733 | 8,735 |
| `Unknown` | 1,686 | 1,492 | 1,448 |
| at the budget | 274 | 80 | 36 |
| steps | 3,096 million | 1,173 million | 572 million |
| the whole run, one job | 382 s to 423 s | 130 s | 36 s |

**Kept.** A run takes 9% of the time it took, which is past the goal of a quarter.

### E3. Two of a `oneOf` share their first

**Hypothesis.** After E2, the most expensive decided check of `oneof-as-anyof` is `o39722`, an `anyOf` of 36 schemas against the same schemas as a `oneOf`: 1,532,379 steps. The negation of a `oneOf` is that none of its terms holds, or two do, and "two hold" is an alternative for each pair: 630 of them, under each of the 36 alternatives of the `anyOf`. A trace has 22,680 such alternatives, all refuted, 14,910 at once and 7,770 after a task for a value. They take 1.07 million of the steps, without the tasks. Each takes two schemas in, and the first of the two is refuted by itself in all pairs but those of one schema: it is taken in anew for each schema after it. The same is 531,000 of the 1,466,563 steps of `additional-as-uneval/o9802`, a `oneOf` of 23 against itself in other words.

**Change.** Two hold when one holds and one after it does. So "two hold" is an alternative for each term but the last, which takes that term in. If it stands, the branch splits at once on the terms after it, before any other disjunction, and that split counts as brought by the alternative, as in E2. The alternatives are followed in the order of the pairs, so the search finds what it found, and a term that is refuted by itself ends all of its pairs. The terms after a place are no term of their own: a `oneOf` would need one for each place, which is the square of its length again.

**Result.** No verdict changes, and 36 checks still end at the budget. The checks that are decided take 180 million steps where they took 212 million. `o39722` takes 458,368 steps and `o9802` 914,026. Sixty schemas that exclude each other, as `anyOf` against `oneOf`, take 105,537 steps where they took 3,200,795: the steps grew with the cube of the length and grow with its square. 1,328 checks take more steps, 110,033 in all and at most 2,901 for one: a first term that stands is settled once by itself and once with each term after it.

### E4. A disjunction that says nothing is not split

**Hypothesis.** After E3, `o9802` takes 914,026 steps, and `oneof-as-anyof/o48661`, a `oneOf` of 11 against the same as `anyOf`, 1,323,338, all in splits on negated conjunctions. A branch that has taken alternative i of the `oneOf` of B holds "not alternative j of B" for every other j, and with "none holds" of the `oneOf` of A also "not alternative j of A" for every j: 45 disjunctions for 23 alternatives. One of them leaves no alternative, the one of A that says what alternative i of B says. Every other says nothing: an object of kind i is of no other kind. But each stands by an alternative, that the property which tells the kinds apart has a value of another kind, and that asks more of the value each time, so each needs a task of its own: 6,520 tasks in one check. The branch splits them in the order in which it met them, 45 deep, before it comes to the one that leaves no alternative, and the counts of E1 do not help: the disjunction that left no alternative under alternative j is one that says nothing under alternative i.

**Change.** Before a branch splits on the negation of a conjunction, it takes the conjunction in on a copy: the complement of the disjunction. If the copy is refuted, every instance of the branch satisfies the disjunction, so the branch goes on without it, with nothing added. This is tried where the branch has another disjunction to split, since a disjunction that says nothing costs by what it does to the others. Three things keep it sound and cheap:

- **The tasks that a try asks for only look for a refutation.** They split, but give no instance, and none of their branches waits for another task. One that comes to a branch which stands, or which would wait, ends with no answer, and the try takes a value to be possible there. So a try costs no witness and goes no deeper than the values that the complement asks about, unless such a task tries a complement of its own.
- **A refutation that rests on a task at work counts for nothing.** A c-reference that is being decided is taken to accept nothing, and what is found that way is kept apart until its task ends. A branch that goes on without a disjunction may give an instance, which is kept for good, so it may not rest on what is not.
- **No complement is tried in a check with a schema that refers to itself in place.** The engine models neither a schema that is negated inside itself nor the negation of one that refers to itself, so of such a schema an instance is not known to satisfy the disjunction or its complement. One pass over the variables finds whether there is such a schema.

**Variants that were dropped.** With ordinary tasks for a try, a check of `rb-testset` that takes 134 steps takes 3.5 million: the complement asks for an array of 32,724 items, and the task builds it. With tasks that do not split, a property of two values that tells the kinds apart is not seen to do so: `o48661` takes 764,915 steps where it takes 150,706. With the complement of an `anyOf` tried as well, no verdict changes and a run takes 1.3 million steps more. With a try at every split, also where no other disjunction is left, the checks of under 10,000 steps take 14% more steps in all, where they take 2% fewer this way.

**Result.** 34 more checks are decided, all `Yes`: every check of `additional-as-uneval` that ended at the budget. None is lost and none is wrong. Two checks still end at the budget, both of `rb-testset`. The checks that were decided before take 116 million steps where they took 212 million. `o9802` takes 141,970 steps, `o39722` 78,924 and `o48661` 150,706. 3,598 checks take more steps, 530,293 in all, at most 15,715 for one.

| | E2 | E3 | E4 |
| --- | ---: | ---: | ---: |
| `Yes` | 23,819 | 23,819 | 23,853 |
| `No` | 8,735 | 8,735 | 8,735 |
| `Unknown` | 1,448 | 1,448 | 1,414 |
| at the budget | 36 | 36 | 2 |
| steps | 572 million | 540 million | 142 million |

**Not timed.** Other work shared the machine during these runs, so E3 and E4 are measured in steps, checks at the budget and verdicts, with eight or four jobs. The time of a run with one job is still to be taken.
