# Speed report: both goals

A run of the benchmark takes **3.4 s where it took 386 s: 112 times faster**. That is one run of the 17,001 cases of corpus 0.8.0 in both directions, 34,002 checks, one after the other. It decides 274 checks more than release 0.4.0 did, loses none, and gives no wrong verdict. The time in the checks went from 377 s to 2.0 s, and the steps of a run, the deterministic count of work, from 3,096 million to 33 million.

This report covers every experiment of this session: the first goal (a quarter of the time; reached at 27 s, then 24 s on a quiet machine) and the second goal (a tenth of that again). It does not replace the first report, which is the summary at the top of [LOG.md](LOG.md) with [chart.html](chart.html). The charts of this one are in [chart-2.html](chart-2.html).

## The changes with the largest relative effect

The factor is the time of a whole run before a change divided by the time after it, in the order in which the changes were made. A change is measured against the state that it was made on, so its factor depends on what came before it. Where an agent also measured a change on its own against the base of the second goal, that is in the text.

| rank | change | kind | a run before → after | factor |
| ---: | --- | --- | --- | ---: |
| 1 | **E2** a dead end counts against the disjunction that brought it | algorithmic | 129.9 s → 35.9 s | **3.62×** |
| 2 | **E1** split first on the disjunction that most often left no alternative | algorithmic | 385.8 s → 129.9 s | **2.97×** |
| 3 | **E9** a disjunction that the branch entails is not split | algorithmic | 23.7 s → 13.1 s | **1.81×** |
| 4 | **both** check the two directions of a case on one load | work shared | 4.69 s → 3.36 s | **1.40×** |
| 5 | **engine** a fast hash, branches that share their parts, no allocation where the engine asks most | same work, cheaper | 8.59 s → 6.25 s | **1.37×** |
| 6 | **merge** one variable for the variables whose terms say the same | algorithmic | 6.25 s → 4.69 s | **1.33×** |
| 7 | **lower** lowering without a string, list or map entry for each schema | same work, cheaper | 10.54 s → 8.59 s | 1.23× |
| 8 | **E7** an instance is handed on to every c-reference that asks no more | algorithmic | 35.6 s → 30.0 s | 1.19× |
| 9 | **strings** the DFA of a format built once for the process | work done once | 12.47 s → 10.54 s | 1.18× |
| 10 | **E8** two alternatives of a `oneOf` share their first | algorithmic | 30.0 s → 26.7 s | 1.12× |
| 11 | **E5** the names of an object cut by all patterns in one product DFA | algorithmic | 36.2 s → 33.1 s | 1.09× |
| 12 | **harness** a schema read once while cases share it, fewer copies | same work, cheaper | 13.43 s → 12.47 s | 1.08× |
| 13 | **E4** an instance kept as what it is made of (structure sharing) | work shared | 35.9 s → 36.2 s | 0.99× |
| 14 | **fallback** a converse that decides nothing is checked again by itself | soundness fix | 3.36 s → 3.45 s | 0.97× |
| 15 | **E6** a property is looked for only where its value can be one | algorithmic | 33.1 s → 35.6 s | 0.93× |

E1 to E8 were timed with other programs at work on the machine (the medians of the first report). From E9 on, every time is the median of three runs on a quiet machine, interleaved, so that a slow minute of the machine falls on every build alike. E9 is measured against E8 on the quiet machine, 23.7 s.

### 1 and 2. In which order a branch splits its disjunctions (E1, E2): 10.7× together

**What was wrong.** 274 checks of 34,002 ended at the budget of 10 million steps and took 89% of the time of a run, 337 s of 377 s. A trace of one showed thrashing, as constraint solvers call it: a branch holds some fifteen disjunctions at once, and one of them has no alternative that stands. The branch split its disjunctions in the order in which it met them, so that one came late and was refuted anew under every combination of alternatives of the disjunctions before it: 745,578 alternatives, 557,806 of them refuted at once.

**The change.** The remedy that constraint solvers have for it, fail-first with a memory of conflicts. E1 counts, for each disjunction, how often it left a branch with no alternative, and a branch splits first on the one with the highest count. E2 counts a dead end inside a disjunction against the disjunction that brought it, so that the count reaches the disjunctions that a branch actually splits. About a hundred lines together.

**The effect.** A run from 386 s to 36 s, 91% of all the time that was ever saved, and 238 more checks decided. This is the outsized change of the whole session: no other change comes near it, and none of the constant-factor work would have mattered while the budget checks took nine tenths of the time.

### 3. A disjunction that the branch entails is not split (E9): 1.81×

**What was wrong.** After E8 the four checks of one schema, o18949, still ended at the budget, and took 5 s of 24 s. Under one alternative of a `oneOf` whose kinds a property tells apart, the negation of every other kind is entailed by the branch, and it was split all the same: each split asked one thing more of the same property, so the c-reference of the value grew by one variable at each level and was decided anew, 17,078 tasks in one check.

**The change.** The dual of unit propagation. Before a branch splits a disjunction, it tests in a copy whether the branch already entails one of its alternatives; if it does, the disjunction is dropped. The test is paid for out of an allowance, twice the steps that it saved before, so that it cannot cost more than a bounded share of a check.

**The effect.** A run from 23.7 s to 13.1 s, the four checks decided, none left at the budget, and the steps of a run from 152 million to 72.5 million. Its review built schemas for which it turns a `No` of 44 steps into `Unknown` (decision 1 below).

### 4. Both directions of a case on one load: 1.40×

**What was wrong.** The harness checks every case in both directions, and each direction parsed, linked and lowered both schemas anew, built the DFAs of their patterns anew and cut the names of their objects anew. Whether a schema accepts a string or how the names of an object are cut is a fact about the schemas, not about the direction.

**The change.** `Checker::check_with_converse(a, b)` loads the two schemas once and checks whether `a` subsumes `b`; it returns that check and a `Converse`, which checks whether `b` subsumes `a` on the same load, with a budget of its own. The converse takes over what the first check worked out about the schemas alone (the terms, the DFAs, the partitions of names, the languages of `propertyNames`, which schemas are definite) and nothing about values.

**The effect.** In the checks 3.27 s → 2.03 s (1.61×), the largest factor of the second goal. The second direction takes 7.0 million steps where a check of its own takes 13.0 million. The first direction is the check itself: the same verdict, reason, counterexample and steps in all 17,001 cases.

**What the review found.** The first version also took over the answers about c-references, and the review built 44 checks that it lost: an instance that the first check found for a schema can be too deep to be put inside another, where a check of its own hands a shallow one on. Those answers are no longer taken over; they were worth 0.7 million of 33 million steps. The run over the adversarial folders then found one check whose converse went down another path and ran out of the budget, where a check of its own decides it in 617,000 steps. So a converse that decides nothing is now checked again by itself (rank 14): it decides at least what a check of its own decides, for 0.3 million steps and some 0.05 s on the corpus.

### 5. The same search in less time (engine): 1.37×

**What was wrong.** A profile at the start of the second goal: the memory allocator was 28% of a run, SipHash 6%, copying a branch for each alternative 5% and dropping it 5%.

**The change.** Three parts, each measured. A hash for the tables of the engine, which multiplies and folds where SipHash does ten rounds; its seed is drawn for each process, so no schema can be written to fall into one bucket (6% of the cycles). The parts of a branch held behind reference counts and copied on the first write, since most alternatives are refuted after touching one part: a copy of a branch now allocates nothing, where it made eight allocations (8%). And no allocation where the engine asks most often: what two c-references say together is kept by the pair, and the search for an object reuses its lists (9%).

**The effect.** In the checks 7.23 s → 4.87 s (1.48×). Every check has the same steps, verdict, reason and counterexample, bit for bit, on the corpus and on 248,096 adversarial checks. On its own against the base it saved 21% of the instructions; after the lowering and string changes it saved a larger share, since what was left was more of the engine.

### 6. One variable for the variables whose terms say the same (merge): 1.33×

**What was wrong.** Two schemas share a variable only when they are written alike. The largest collection of the corpus, 62% of the time in the checks, is pairs that say the same in other words: an object closed by `additionalProperties: false`, against the same object closed by a second schema beside it under an `allOf`. Lowered, the two are the same conjunction of the same terms, reached through other variables and in another order, and the engine worked out by search what a canonical form shows at once.

**The change.** Each variable gets a canonical term: conjunctions and disjunctions flattened through the variables that they refer to, their parts as a set in one order, terms that say nothing left out, a double negation removed, `oneOf` and leaves kept as they are. Variables with equal canonical terms are one class; those on a cycle through a property or an item are told apart by partition refinement, the coarsest bisimulation, which is the standard way to decide the equality of recursive types. Of each class one variable stands for the others, and `x and not x` is then refuted by identity.

**The effect.** In the checks 4.87 s → 3.27 s (1.49×). The steps of a run go from 72.5 million to 39.2 million, and 14,872 checks have one variable for A and B at the root, where 3,120 had. On its own against the base it took the checks from 11.4 s to 7.3 s under load.

**What the review found.** The variable that stood for a class could be a large term that comes to `true` or `false`; the engine then unfolded it where it knows `true` and `false` at once, and five constructed checks ended at the budget. A variable whose term is `true` or `false` itself now stands for those classes, and all five are decided again at the base's steps.

### The rest, in short

- **lower (1.23×).** Lowering gave each schema a JSON string to class it by, a list and a map entry. It now writes a length-prefixed description into one reused buffer, keeps the successors of the schemas in one flat array, and copies a key only when it is new. Lowering 3.68 s → 1.91 s. Its agent first measured whether to lower only the terms that the engine opens: the engine looks at 84% of them, so that would save 0.1 to 0.3 s and change the order of the ids, and it was not built.
- **E7 (1.19×).** An instance found for a c-reference is handed on to the c-references that ask no more of it, so they are not decided again.
- **strings (1.18×).** A run built the DFA of a format 3,203 times, for 14 patterns: 1.26 s and 9.3 million steps. It is now built once for the process, and each check that needs it is still charged its steps, so the steps of a check do not depend on what was checked before. A plain word between `^` and `$`, 244,240 of them in a run, is read without the parser.
- **E8 (1.12×).** The negations of the pairs of a `oneOf` share their first alternative, so the disjunction of "two of them hold" is factored and not split pair by pair.
- **E5 (1.09×).** The names of an object are cut by all of its patterns in one product DFA, with a guard that falls back to cutting one by one where the product would grow past the sum of the states.
- **harness (1.08×).** The time outside the checks went from 2.4 s to 1.5 s: a schema that the case before had is not read again, one validator per schema serves both directions, and no counterexample or record is copied. The first part depends on the corpus putting the paired cases next to each other.
- **E4, E6 and the fallback** cost a little time. E4 shares the parts of an instance and was kept for the steps it saves. E6 halves the steps of a run and decides 30 more checks, and makes a run 2.5 s slower, because the steps it saves were the cheapest ones. The fallback is the price of a guarantee.

## Where the time goes now

A run takes 3.45 s: 2.04 s in the checks and 1.41 s around them. The harness is now 41% of the run. A profile of the merged build puts 19% of the process in reading the cases and 15% in building the validators of the `jsonschema` crate that confirm each counterexample. In the checks, `Objects::left` is 5.4% of the process, where it was 21% at the start of the second goal, and `Strings::is_empty` 7%.

**The second goal was a tenth of the time: a run under 3 s, from 27 s when it was set.** A run takes 3.45 s, 7.8 times faster than 27 s and 3.9 times faster than the 13.4 s at which E9 was merged. The checks alone take 2.0 s. What is left of the harness is the largest single part, and it is not the library.

## What was tried and not kept

- **E3:** other rules for which disjunction to split first. None beat E1 and E2; see LOG.md.
- **A factored `oneOf` that gave a wrong `No`** (the branch `perf/exp-o98xx-oneof`): it passed every test and the corpus, and its review found a wrong verdict. It is kept as a record only.
- **Unit propagation by looking ahead,** tried for o18949: it decided the four checks and cost more elsewhere than it saved in every variant. E9 is the variant that pays.
- **Lazy lowering:** measured, not built (see lower above).
- **The objects branch** (`perf/x-object-questions`): keep the answer to a question about objects by what it asks. Its first commit is sound and saved 4.4% of the instructions at the base; its second saves 1.5% more and lets a 122 kB input take 4.5 GB. After the other changes, `Objects::left` is 5.4% of a run, and the branch conflicts with the engine branch in 640 lines of `object.rs`. Not merged.
- **Classing again only the schemas that a cycle leads to** (commit `2a1c6ab` of the lowering branch): correct, and no gain that its review could measure. Reverted.
- **The converse taking over the answers of the first check:** lost 44 verdicts on constructed schemas. Removed.
- **A random factor in the hash:** for one draw in four, ids in a row fell into few values in the high bits, and a test failed one run in four. The factor is now the golden ratio, as in foldhash, and only the seed is random.

## Decisions for the owner

Each of these gives up something, simplicity or a rule of the design, for speed.

1. **E9 can lose a verdict on constructed schemas.** Its cost review built schemas for which the entailment test steers the search so that a `No` of 44 steps becomes `Unknown`. No variant kept the gain without that. On 181,000 checks outside the corpus, E9 against the first goal's end is 30 verdicts gained and 6 lost.
2. **A new public API.** `Checker::check_with_converse(&a, &b) -> Result<(Check, Converse<'s>), Error>`, and a public `Converse<'s>` with `check(self) -> Check`. It borrows both schemas and is not `Send`. Its steps can be up to twice the budget, where the fallback checks it again; its counterexample is another valid instance in 6 cases of the corpus.
3. **Something outlives a check.** The DFAs of the formats are kept for the process in a map behind a lock, and the store holds DFAs by `Arc`. The first check that needs one builds it whatever its budget (at most about 2.4 ms). A Python program that forks while another thread holds the lock can hang in the child; one `OnceLock` per format would remove that, and it is noted in DESIGN.md.
4. **The merging of variables is about 1,000 lines,** charges nothing to the budget (it stops at 256 times the size of the terms and merges nothing then), and changes the order of the search: 195 checks of the corpus take more steps, and in 66,000 random checks one `Yes` went from 9.6 million to 11.7 million steps and so past the budget.
5. **Branches share their parts by reference counts,** written only through `Rc::make_mut`; the search for an object keeps its lists from one search to the next; the crate has its own hash, about 60 lines.
6. **The description that classes a schema is length-prefixed bytes,** no longer readable text.
7. **The harness reuses a schema's text from the last case,** which pays because the corpus puts paired cases next to each other.

## How this was checked

- **The corpus.** Every change was run over the whole corpus with no verdict lost, none flipped and no counterexample refused by the validator. The final build has the verdicts of E9 in all 34,002 checks: 23,853 `Yes`, 8,737 `No`, 1,412 `Unknown`, none at the budget.
- **Tests.** `cargo test --workspace` passes in debug and release, `pytest` of the Python package passes (48), `cargo fmt` is clean, and clippy has one warning, which `main` has too.
- **Reviews.** Each change of the second goal was built by one agent and reviewed by another that tried to break it, with schemas of its own and a random differential test of 20,000 checks or more. Four of seven reviews found a problem (lost verdicts in merge and both, a test that failed one run in four, a harness that read one file the base refuses), and each was fixed before the merge and given a regression test.
- **The adversarial folders.** All 54 folders that reviewers built across both goals, base against the merged build. 41 are done: 0 wrong, 0 flipped, and one lost verdict, which the fallback fixed. The other 13 are still running.
- **Found on the way, not fixed:** a panic that is on `main` too. A schema whose resource root binds a `$dynamicAnchor` and has no subschema of its own crashes the check in `src/lower/scopes.rs`, and the Python package raises `PanicException` where it promises to return `Unknown`. A reproducer is in the lowering review.

## Where everything is

- `perf/trunk`: the first goal, E1 to E8. `perf/exp-entailment`: E9.
- `perf/x10`: the second goal, E9 and the six merged branches with the fixes of their reviews.
- `perf/x-*`: what each agent of the second goal built, as it built it, also the objects branch.
- [LOG.md](LOG.md): the log of every experiment; [timings.csv](timings.csv): every timed run of the first goal; this report's timings are below.

### The timings of the second goal

Three interleaved runs of each build on a quiet machine, one job, the whole run and the time in the checks, in seconds.

| build | commit | run 1 | run 2 | run 3 | median | checks (median) | steps |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| E9 merged | `7e3686b` | 15.28 | 13.43 | 13.03 | 13.43 | 11.17 | 72,544,068 |
| + harness | `a272481` | 13.85 | 12.47 | 12.43 | 12.47 | 11.07 | 72,544,068 |
| + strings | `67433c0` | 11.94 | 10.29 | 10.54 | 10.54 | 9.06 | 72,544,068 |
| + lowering | `e4c2d43` | 10.27 | 8.59 | 8.55 | 8.59 | 7.23 | 72,544,068 |
| + engine | `e7e4dd0` | 6.73 | 6.07 | 6.25 | 6.25 | 4.87 | 72,544,068 |
| + merge, with its fix | `dc6ee5a` | 4.69 | 4.45 | 4.69 | 4.69 | 3.27 | 39,212,646 |
| + both, with its fix | `3fa8942` | 3.43 | 3.23 | 3.36 | 3.36 | 2.03 | 32,907,748 |
| final, with the fallback | `735461e` | 4.02 | 3.36 | 3.45 | 3.45 | 2.04 | 33,214,875 |

The first round of runs started at a load average of 5.4, which is why its numbers are higher; the other two began at 1.8 to 3.4. E9 merged took 13.1 s in the session in which it was merged (13.10, 13.09 and 13.13 s) and 13.4 s in this one; the chart takes 13.1 s for E9 and measures each change of the second goal against this session's runs.
