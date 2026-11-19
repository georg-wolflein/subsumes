# Speed experiments

A log of the experiments of step 8, "Speed": what was tried, why, and what it did to a run over the corpus. The goal is a run that takes a quarter of the time or less.

## Summary

A run takes 27 s where it took 386 s: 7% of the time, with 270 more checks decided, none lost and none wrong.

| | commit | what | a run | of the baseline | steps | at the budget | `Unknown` |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: |
| baseline | `9e48b0d` | release 0.4.0 | 385.8 s | 100% | 3,096 million | 274 | 1,686 |
| E1 | `3caefd6` | split first on the disjunction that most often left no alternative | 129.9 s | 33.7% | 1,173 million | 80 | 1,492 |
| E2 | `2e2e3fa` | count a dead end against the disjunction that brought it | 35.9 s | 9.3% | 572 million | 36 | 1,448 |
| E4 | `e3e7ccb` | keep an instance as what it is made of | 36.2 s | 9.4% | 532 million | 34 | 1,446 |
| E5 | `700c107` | cut the names of an object by all patterns in one product | 33.1 s | 8.6% | 495 million | 34 | 1,446 |
| E6 | `2db7cec` | look for a property only where its value can be one | 35.6 s | 9.2% | 225 million | 4 | 1,416 |
| E7 | `fc470ea` | an instance is one of every c-reference that asks no more | 30.0 s | 7.8% | 185 million | 4 | 1,416 |
| E8 | `11d937e` | two of a `oneOf` share their first | 26.7 s | 6.9% | 152 million | 4 | 1,416 |

- **Two changes are nearly all of it.** E1 and E2 are one idea, about a hundred lines together: in which order a branch splits its disjunctions. They take a run from 386 s to 36 s, 91% of the time, and decide 238 checks. The checks that ended at the budget thrashed, and the remedy is the one that constraint solvers have for it.
- **The second round is worth more in verdicts and steps than in time.** E4 to E8 decide 32 more checks and take the steps of a run from 572 million to 152 million, and the time from 36 s to 27 s. E6 alone halves the steps and makes a run 2.5 s slower: what it saves were the cheapest steps, and the four checks that are left at the budget spend theirs on dearer work.
- **What is left.** Of the 24 s that the checks of a run take, 5 s are those four checks, of one schema. E9 decides them and is not kept; see there. About 7 s are the 33,500 checks that take less than 3 ms each, and 3 s of a run are outside the checks: reading the cases, validating the counterexamples and writing the results.
- **E3 and E9** are experiments that were not kept, and each has its entry below.

The time of a run is the median of three or four runs with one job. A run on a machine with nothing else at work takes about a tenth less: 24 s for E8 and 32 s for E2.

## How a run is measured

- **The run.** `make benchmark`, which checks the 17,001 cases of corpus 0.8.0 one after the other, in both directions: 34,002 checks. The time is the wall-clock time of the whole run, and "in the checks" is the sum of the times of the checks, which leaves out reading the cases, validating the counterexamples and writing the results.
- **The machine.** An Apple M3 Pro with 11 cores. Other programs were at work on it during the runs, among them a virtual machine that used four to five cores, so a time is good to a few percent and no better. The load before each run is in `timings.csv`.
- **Verdicts first.** An experiment is kept only if no check loses its verdict, none is wrong and no counterexample is refused by the validator. That is seen with `make benchmark JOBS=8`, whose times are no more than a hint. The time of an experiment is then measured with one job.
- **The tests.** `cargo test --workspace` passes for every experiment that is kept.
- **`timings.csv`** has one line for each timed run. The runs were made in three sessions: the first with the baseline, E1 and E2 as they were made, the second with every experiment in turn three times, and the third on the machine with nothing else at work.

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

### E3. Other rules for which disjunction to split first

**Hypothesis.** The count of E1 and E2 is one of several rules that constraint solvers use. Another may decide more checks or take fewer steps: the disjunction whose dead end was the last one, in place of the one with the most, or the disjunction with the fewest alternatives where the counts are equal.

**Change.** Four variants of the rule behind a switch, each run over the whole corpus. Steps do not depend on the machine, so the runs are held against each other by steps and verdicts.

| rule | steps | `Unknown` |
| --- | ---: | ---: |
| most dead ends, then first met (E2) | 571.5 million | 1,448 |
| last dead end, then first met | 564.3 million | 1,448 |
| most dead ends, then fewest alternatives | 698.7 million | 1,454 |
| last dead end, then fewest alternatives | 718.0 million | 1,454 |

**Dropped.** The last dead end takes 1.3% fewer steps than the count and decides the same checks, which is no reason to change the rule. The fewest alternatives first loses 6 verdicts and takes 22% more steps: the order in which the disjunctions are met is the better one where nothing is known of them.

### How the steps grow, on a schema made for it

A `oneOf` of n kinds of object, each with a property of its own that it requires, written in two ways: A closes each kind with a second schema beside the first, as the corpus does where `unevaluatedProperties` was written out, and B closes it in the schema itself. Both say the same, so both checks are `Yes`. It is the unit test `a_disjunction_that_leaves_no_alternative_is_split_before_the_others`, and what `additional-as-uneval/o81108` comes down to.

Steps of the check that A subsumes B:

| kinds | baseline | E1 | E2 |
| ---: | ---: | ---: | ---: |
| 4 | 32,563 | 13,183 | 2,839 |
| 5 | 231,300 | 65,712 | 5,434 |
| 6 | 1,773,709 | 374,404 | 9,908 |
| 7 | at the budget | 1,921,296 | 16,578 |
| 8 | at the budget | 9,381,607 | 24,999 |

- The baseline takes seven to eight times the steps for each kind that is added, and E1 five times: both are exponential, and E1 only has the smaller base.
- E2 takes less than twice the steps for each kind that is added, and less with each one, 1.9 times for the fifth and 1.5 times for the eighth: the steps grow with about the third power of the number of kinds.

## The second round

After E2 a run takes 36 s, and what is left is of another kind. So the second round began with a look at where the time goes, by eight agents at once, each in a checkout of its own: one for each group of checks that were still slow, and one with a profiler. Each was to find the cause, propose a remedy that follows from how the search works and not from one schema, build it, and hold it against the tests and the whole corpus. A reviewer then took each change that was built and tried to break it: by reading it, by schemas written to expose a flaw, and by thousands of pairs made at random, held against the version before.

What the reviewers found is why this is worth its cost. Of eight changes, four were sound as they stood, two lost verdicts on inputs outside the corpus and were mended before they were kept, one was sound but slower, and one gave a wrong `No`.

What the agents found:

- **The search for an object thrashes as the splits did.** Four agents came to this from four groups of checks. A property that there has to be is tried at every fragment of its language, and the one that has no place is tried late, under every placement of those before it. In an object that takes no property but those that it names, 96% to 98% of the places tried are fragments in which no property can have a value. Of the 572 million steps of a run, 336 million were places tried.
- **The names of an object are cut by one pattern after the other.** A schema with 122 names that hold a dot, written as patterns, took 15,000 products of DFAs to cut its names into 123 parts: 6.85 of the 6.93 million steps of each of its checks.
- **An instance is copied into everything that holds it.** A counterexample of 3.5 million values was built for each c-reference that it is one of, and copied once for each level around it.
- **A branch waits for a chain of c-references,** each of which names every variable of the one before, and each was a task.
- **The negation of a `oneOf` takes its first schema in anew for each pair.**
- **Most disjunctions that are split say nothing in their branch.** This is the largest cause that is left; see E9.

The time of each experiment below is the median of three runs with one job, made one after the other on the same evening, with the experiments taken in turn so that a change in the load meets all of them.

### E4. An instance is kept as what it is made of

**Hypothesis.** `rb-testset/s189` and `s199` end at the budget in 30 ms to 70 ms: the steps are not spent on search. An instance was built as a JSON value as soon as a task found it, and every object or array that holds it copied it, at a step for each value inside. The counterexample of s189 has 3.5 million values, and 99.96% of the steps of the check were copies.

**Change.** `e3e7ccb`. An instance holds its values by reference, and an array holds the one value of all positions after its first ones once, with their count. Only the counterexample of the check is written out, at a step for each value inside it.

**Review.** Sound. Nothing in the search reads what an instance holds, so every check takes the path it took, and no check takes more steps. On 8,000 checks made at random no verdict is lost and every counterexample is the same.

**Result.** The two checks are decided, `No` with a counterexample that the validator confirms. The collection takes 14.4 million steps where it took 54.0 million, and a run 532 million where it took 572 million. In time it is nothing: the steps that are saved were the cheapest there are.

### E5. The names of an object are cut by all patterns in one product

**Hypothesis.** `additional-as-uneval/o19184` takes 6.9 million steps in each of its four checks, also in the two that end in `No`, with 75 splits. One call that cuts the names by 122 patterns takes 98.9% of them. Cut by one pattern after the other, each part so far is intersected with the pattern and with its complement: two products for every part and pattern, which for patterns that share no name is the square of their number.

**Change.** `426945a`, `700c107`. One product of the DFAs of all the patterns, as a lexer has for its tokens: which of them accept in a state says which part a string is of. The DFA of a part is the product with the states of the part accepting, written down as far as its states lead to one of them.

**Review.** Sound, and not better on every input. Two lists of patterns outside the corpus lose verdicts. Counters of different lengths have a product with a state for every combination, where each part stays small: a check that took 26,000 steps ended at the budget. And many patterns that share strings make many parts, each of which is read off the whole product. So the product is given up when it has more states than the DFAs have together, which patterns that share no string never exceed, and the list is then cut as before. With that, 8,000 checks made at random by the reviewer's generator, whose patterns all share strings, lose no verdict and take 2.0% to 2.5% more steps, which is what the products cost that are given up.

**Result.** No verdict changes. o19184 takes 184,000 steps where it took 6.9 million, and a run 495 million where it took 532 million. The eight checks of the two schemas that were looked at take 0.1 s together where they took 2.7 s.

### E6. A property is looked for only where its value can be one

**Hypothesis.** The 34 checks that are left at the budget spend 87% to 99% of their steps on places tried by the search for an object. With `additionalProperties: false`, the names of every other schema of the branch are fragments in which no property can have a value, and each negated schema of the other side asks for a property that is outside its names, which may be in any of them. Such a property has two or three fragments that take it, and one of them has none.

**Change.** `02af4f1`, `2db7cec`. A fragment whose properties satisfy nothing is no place for a property that there has to be. A property that is left with no fragment leaves no object, which is seen before the search begins. 22 lines.

**Three other remedies for the same cause** were built by other agents and are not kept, since this one is the simplest and takes the fewest steps:

| remedy | branch | steps of a run, on E2 | review |
| --- | --- | ---: | --- |
| leave out the fragments that take no value (kept) | `perf/exp-profile` | 302.0 million | sound |
| the same, and those that clash with what the property is asked | `perf/exp-o18949` | 302.0 million | sound |
| where a property runs out of places, look at it alone | `perf/exp-o99xx` | 324.8 million | sound |
| conflict-directed backjumping | `perf/exp-o2137x` | 320.3 million | sound, and slower: what it keeps for each level takes more time than the steps say |

Each of the four decides the same 30 checks.

**Review.** Sound: 78,000 checks made at random and 42 written by hand give the same verdicts. The change had also placed the properties with the fewest fragments left first. The reviewer found that this decides nothing more and takes more steps in a few checks, so the order is the one of before.

**Result.** 30 checks are decided, all `Yes`. A run takes 225 million steps where it took 495 million, and 4 checks still end at the budget. **And a run takes 2.5 s longer.** The 30 checks ended at the budget in 0.2 s to 0.4 s each, because a place tried is the cheapest step there is, so deciding them saves little. The four that are left, of the schema o18949, now spend their ten million steps on the work of the engine, which takes four to five times as long: 1.3 s to 1.6 s each where they took 0.3 s, 5.6 s together where they took 1.2 s. Steps are not time.

### E7. An instance is one of every c-reference that asks no more

**Hypothesis.** With E6 in, 63% of the steps of the checks that it decided are in tasks for a c-reference that names only variables of one that already has an instance. The search for an object asks what the values at one place are asked together each time one more shares the place, so a branch waits for `[M, not M1]`, `[M, not M1, not M2]` and so on.

**Change.** `fc470ea`, `11d937e`. The c-reference that names the most is decided first. When it has an instance, every other one that the branch waits for and that names only variables of it has that instance too, and gets no task.

**Review.** Not sound as it stood, in that it loses a verdict: the instance that is handed on may be nested far deeper than the one that a task of its own gives, here 127 levels where `null` would do, and an object that holds it is then too deep to give. The check answered `Unknown` where it had answered `No`. To hand on only values that hold no other keeps none of the gain, since the values in question are objects. So where a value was passed over for its depth and an instance had been handed on, the check is now made again without handing any on. The reviewer's case is a test.

**Result.** No verdict changes. A run takes 185 million steps where it took 225 million.

### E8. Two of a `oneOf` share their first

**Hypothesis.** The negation of a `oneOf` of n schemas is "none holds, or two do", and "two do" was an alternative for each pair. Under each alternative of the other side, the first schema of nearly every pair is refuted by itself, and was taken in again for each schema that it is paired with: 22,680 alternatives in one check of `oneof-as-anyof/o39722`, every one of them refuted. The steps grow with the cube of the length.

**Change.** `f79889b`. "Two do" is one alternative for each schema but the last: that schema holds, and one of those after it. It is the same pairs in the same order, and a schema that is refuted is refuted once.

**Review.** Sound: it says the same as before.

**Result.** No verdict changes. A run takes 152 million steps where it took 185 million.

### E9. A disjunction that the branch entails is not split (not kept)

**Hypothesis.** Under one alternative of a `oneOf` whose kinds a property tells apart, the negation of every other kind is entailed. It is split all the same, and its alternative that stands asks one thing more of the same property, so the c-reference of the value grows by one variable at each level and is decided anew: 17,078 tasks in one check of o17072. The counts of E1 do not help where the dead end is another disjunction under each alternative, which is why the four checks of o18949 still end at the budget.

**Change.** Before a split, take in the opposite of every alternative of the disjunction in a copy of the branch. If the copy is refuted, the branch entails the disjunction, which is dropped. This is the dual of unit propagation, and what the plan of the design calls a c-reference that says no more than a smaller one. Two agents built it.

- `perf/exp-o98xx-oneof` (`367d17a`): a run takes 142 million steps where it took 572 million, and 2 checks end at the budget where 36 did. **It is wrong.** The reviewer wrote a schema that holds itself in a property, for which it answers `No` with a counterexample that B rejects. It took an answer that holds only while a task is at work for one that holds for good, where the copy waits for another task in between.
- `perf/exp-o17072-o358` (`d8c01b1`): 138 million steps, and 1 check at the budget. It makes the test only for schemas that lead to no cycle and to no leaf that holds a schema. The reviewer found no wrong verdict in 50,000 checks made at random and by hand, and the first one's counterexample does not break it. But nothing bounds what the test costs: a check that took 9 steps ended at the budget. And every split pays for it, which is a third more steps for the checks under 1,000 steps.

**Not kept.** It is the largest gain that is left: the four checks of o18949 are 5 s of the 24 s that the checks of a run take, and o17072 another second. It is also 300 lines with a second kind of task, in the part of the engine where a mistake is a wrong verdict, as the first of the two shows. It needs an allowance for the test before it can be kept, and a decision whether it is worth what it adds.

### Also tried and dropped

- **Unit propagation by looking ahead** (the agent of o18949): after a branch has taken in what needs no split, try the alternatives of every disjunction in a copy until two stand. It decides the four checks of o18949, and in every variant it costs more elsewhere than it saves or loses a verdict: the copy and the search for an object are paid for every disjunction at every node.
- **A smaller budget.** With E8 in, no check that is decided takes more than 3.6 million steps, so a budget of 4 million would lose no verdict of the corpus and save 3 s of a run. The budget is not changed here: it is a setting of the library and not a part of these experiments.
