//! A run as the benchmark comment of a pull request, compared with the run of the base branch.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::counterexample::Confirmation;
use crate::results::{Counts, Direction, Outcome, Record};

/// The label on a pull request that accepts checks lost to `Unknown`.
pub const LABEL: &str = "allow-lost-verdicts";

/// At most this many entries per list: GitHub caps a comment at 65,536 characters.
const LIST_LIMIT: usize = 40;
const TABLE_LIMIT: usize = 10;

/// The run of the base branch.
pub struct Base<'a> {
    pub records: &'a [Record],
    /// What to call it in the comment: the short hash of its commit.
    pub label: &'a str,
}

pub struct Comparison {
    /// The comment, as Markdown.
    pub comment: String,
    /// The checks that the base decided and this run answers with `Unknown` or an error.
    pub lost: usize,
}

/// A check in the base run and in this run.
type Pair<'a> = (&'a Record, &'a Record);

struct Changes<'a> {
    decided: Vec<Pair<'a>>,
    lost: Vec<Pair<'a>>,
    flipped: Vec<Pair<'a>>,
    steps: Vec<Pair<'a>>,
    only_head: usize,
    only_base: usize,
}

impl<'a> Changes<'a> {
    fn between(head: &'a [Record], base: &'a [Record]) -> Self {
        let before: HashMap<(&str, Direction), &Record> =
            base.iter().map(|record| (record.key(), record)).collect();
        let mut changes = Self {
            decided: Vec::new(),
            lost: Vec::new(),
            flipped: Vec::new(),
            steps: Vec::new(),
            only_head: 0,
            only_base: base.len(),
        };
        for after in head {
            let Some(&before) = before.get(&after.key()) else {
                changes.only_head += 1;
                continue;
            };
            changes.only_base -= 1;
            let pair = (before, after);
            match (before.outcome.is_decided(), after.outcome.is_decided()) {
                (false, true) => changes.decided.push(pair),
                (true, false) => changes.lost.push(pair),
                (true, true) if before.outcome.label() != after.outcome.label() => {
                    changes.flipped.push(pair);
                }
                _ => {}
            }
            if before.steps != after.steps {
                changes.steps.push(pair);
            }
        }
        changes
            .steps
            .sort_by_key(|(before, after)| std::cmp::Reverse(before.steps.abs_diff(after.steps)));
        changes
    }
}

pub fn compare(head: &[Record], base: Option<&Base>, allow_lost: bool) -> Comparison {
    let changes = base.map(|base| Changes::between(head, base.records));
    let mut parts = vec!["## Benchmark".to_owned()];
    parts.push(match base {
        Some(base) => format!("Compared with `{}` on the base branch.", base.label),
        None => "There are no results of the base branch to compare with.".to_owned(),
    });
    parts.push(tally(head, base));
    parts.push(totals(head, base, changes.as_ref()));
    parts.extend(counterexamples(head));
    parts.extend(failures(head));
    if let Some(changes) = &changes {
        parts.extend(lost(&changes.lost, allow_lost));
    }
    parts.push(reasons(head, base));
    if let Some(changes) = &changes {
        parts.extend(verdict_changes(changes));
        parts.extend(step_changes(&changes.steps));
    }
    parts.extend(most_expensive(head));
    Comparison {
        comment: parts.join("\n\n") + "\n",
        lost: changes.map_or(0, |changes| changes.lost.len()),
    }
}

/// The verdicts per collection, each with its change against the base.
fn tally(head: &[Record], base: Option<&Base>) -> String {
    let now = per_collection(head);
    let before = base.map(|base| per_collection(base.records));
    let mut rows = Vec::new();
    for (collection, counts) in &now {
        let before = before
            .as_ref()
            .map(|before| before.get(collection).copied().unwrap_or_default());
        rows.push(tally_row(
            format!("`{collection}`"),
            counts,
            before.as_ref(),
        ));
    }
    let before = base.map(|base| Counts::of(base.records));
    rows.push(tally_row(
        "**total**".to_owned(),
        &Counts::of(head),
        before.as_ref(),
    ));
    table(
        &[
            "collection",
            "checks",
            "Yes",
            "No",
            "Unknown",
            "wrong",
            "errors",
        ],
        &rows,
    )
}

fn per_collection(records: &[Record]) -> BTreeMap<&str, Counts> {
    let mut collections: BTreeMap<&str, Counts> = BTreeMap::new();
    for record in records {
        collections
            .entry(record.collection())
            .or_default()
            .add(record);
    }
    collections
}

fn tally_row(name: String, now: &Counts, before: Option<&Counts>) -> Vec<String> {
    let cell = |count: fn(&Counts) -> u64| with_change(count(now), before.map(count));
    vec![
        name,
        cell(|counts| counts.checks),
        cell(|counts| counts.yes),
        cell(|counts| counts.no),
        cell(|counts| counts.unknown),
        cell(|counts| counts.wrong),
        cell(|counts| counts.errors),
    ]
}

/// The steps and the time of the whole run.
fn totals(head: &[Record], base: Option<&Base>, changes: Option<&Changes>) -> String {
    let now = Counts::of(head);
    let before = base.map(|base| Counts::of(base.records));
    let mut text = format!(
        "The checks took {} steps in total and {}",
        with_change(now.steps, before.map(|before| before.steps)),
        seconds(now.nanos),
    );
    if let Some(before) = before {
        text += &format!(", against {} on the base branch", seconds(before.nanos));
    }
    text += ". Steps are exact; times vary from one runner to the next.";
    if let Some(changes) = changes
        && changes.only_head + changes.only_base > 0
    {
        text += &format!(
            " The two runs are not over the same checks: {} only in this run, {} only in the base.",
            number(changes.only_head as u64),
            number(changes.only_base as u64),
        );
    }
    text
}

/// What a validator made of the counterexamples. One that is none is a wrong verdict and
/// named among the failures; one that was not looked at is named here, with the reason.
fn counterexamples(head: &[Record]) -> Option<String> {
    let counts = Counts::of(head);
    if counts.no == 0 {
        return None;
    }
    let mut text = format!(
        "A validator confirms {} of {}.",
        number(counts.confirmed),
        plural(counts.no as usize, "counterexample"),
    );
    let unchecked: Vec<String> = head
        .iter()
        .filter_map(|record| match &record.outcome {
            Outcome::No {
                confirmation: Confirmation::NotChecked(why),
                ..
            } => Some(format!("{}: {why}", record.name())),
            _ => None,
        })
        .collect();
    if !unchecked.is_empty() {
        let heading = format!("{} not checked", plural(unchecked.len(), "counterexample"));
        text += &format!("\n\n{}", details(&heading, &bullets(&unchecked)));
    }
    Some(text)
}

/// What fails the run whatever the base says: wrong verdicts and errors.
fn failures(head: &[Record]) -> Vec<String> {
    let mut parts = Vec::new();
    let wrong: Vec<String> = head
        .iter()
        .filter(|record| record.is_wrong())
        .map(Record::described)
        .collect();
    if !wrong.is_empty() {
        let heading = plural(wrong.len(), "wrong verdict");
        parts.push(format!("### :x: {heading}\n\n{}", bullets(&wrong)));
    }
    let errors: Vec<String> = head
        .iter()
        .filter(|record| record.is_error())
        .map(Record::described)
        .collect();
    if !errors.is_empty() {
        let heading = plural(errors.len(), "error");
        parts.push(format!("### :x: {heading}\n\n{}", bullets(&errors)));
    }
    parts
}

/// The checks that the base decided and this run does not.
fn lost(pairs: &[Pair], allowed: bool) -> Option<String> {
    if pairs.is_empty() {
        return None;
    }
    let (mark, consequence) = if allowed {
        (":warning:", format!("The label `{LABEL}` accepts them."))
    } else {
        (
            ":x:",
            format!(
                "The job fails for them. To accept them, add the label `{LABEL}` to the pull request and run the job again."
            ),
        )
    };
    let heading = format!("{} lost to Unknown", plural(pairs.len(), "check"));
    Some(format!(
        "### {mark} {heading}\n\n{consequence}\n\n{}",
        bullets(&transitions(pairs))
    ))
}

/// The reasons for `Unknown`, counted.
fn reasons(head: &[Record], base: Option<&Base>) -> String {
    let now = per_reason(head);
    let before = base.map(|base| per_reason(base.records));
    let mut names: BTreeSet<&str> = now.keys().copied().collect();
    if let Some(before) = &before {
        names.extend(before.keys().copied());
    }
    let mut names: Vec<&str> = names.into_iter().collect();
    names.sort_by_key(|name| std::cmp::Reverse(now.get(name).copied().unwrap_or(0)));
    let rows: Vec<Vec<String>> = names
        .into_iter()
        .map(|name| {
            let count = now.get(name).copied().unwrap_or(0);
            let before = before
                .as_ref()
                .map(|before| before.get(name).copied().unwrap_or(0));
            vec![format!("`{name}`"), with_change(count, before)]
        })
        .collect();
    let body = if rows.is_empty() {
        "None.".to_owned()
    } else {
        table(&["reason", "checks"], &rows)
    };
    details(
        &format!("Reasons for Unknown ({})", plural(now.len(), "reason")),
        &body,
    )
}

fn per_reason(records: &[Record]) -> BTreeMap<&str, u64> {
    let mut reasons = BTreeMap::new();
    for record in records {
        if let Outcome::Unknown { reason, .. } = &record.outcome {
            *reasons.entry(reason.as_str()).or_default() += 1;
        }
    }
    reasons
}

/// The checks whose verdict changed without being lost.
fn verdict_changes(changes: &Changes) -> Vec<String> {
    let mut parts = Vec::new();
    if !changes.decided.is_empty() {
        let heading = format!(
            ":white_check_mark: {} newly decided",
            plural(changes.decided.len(), "check")
        );
        parts.push(details(&heading, &bullets(&transitions(&changes.decided))));
    }
    if !changes.flipped.is_empty() {
        let heading = format!(
            ":warning: {} changed between Yes and No",
            plural(changes.flipped.len(), "check")
        );
        parts.push(details(&heading, &bullets(&transitions(&changes.flipped))));
    }
    parts
}

/// The checks whose steps changed most.
fn step_changes(pairs: &[Pair]) -> Option<String> {
    if pairs.is_empty() {
        return None;
    }
    let rows: Vec<Vec<String>> = pairs
        .iter()
        .take(TABLE_LIMIT)
        .map(|(before, after)| {
            vec![
                after.name(),
                number(before.steps),
                number(after.steps),
                change(after.steps, before.steps),
            ]
        })
        .collect();
    let heading = format!(
        "{} with a different number of steps",
        plural(pairs.len(), "check")
    );
    Some(details(
        &heading,
        &table(&["check", "base", "now", "change"], &rows),
    ))
}

/// The checks that took the most steps.
fn most_expensive(head: &[Record]) -> Option<String> {
    let mut costly: Vec<&Record> = head.iter().filter(|record| record.steps > 0).collect();
    if costly.is_empty() {
        return None;
    }
    costly.sort_by_key(|record| std::cmp::Reverse(record.steps));
    let rows: Vec<Vec<String>> = costly
        .iter()
        .take(TABLE_LIMIT)
        .map(|record| vec![record.name(), record.outcome.label(), number(record.steps)])
        .collect();
    Some(details(
        "The checks that took the most steps",
        &table(&["check", "verdict", "steps"], &rows),
    ))
}

fn transitions(pairs: &[Pair]) -> Vec<String> {
    pairs
        .iter()
        .map(|(before, after)| {
            format!(
                "{}: {} to {}",
                after.name(),
                before.outcome.label(),
                after.outcome.label()
            )
        })
        .collect()
}

/// A Markdown table whose first column is text and whose other columns are numbers.
fn table(header: &[&str], rows: &[Vec<String>]) -> String {
    let mut align = vec!["---"; header.len()];
    align[1..].fill("---:");
    let mut lines = vec![
        format!("| {} |", header.join(" | ")),
        format!("| {} |", align.join(" | ")),
    ];
    lines.extend(rows.iter().map(|row| format!("| {} |", row.join(" | "))));
    lines.join("\n")
}

fn details(summary: &str, body: &str) -> String {
    format!("<details>\n<summary>{summary}</summary>\n\n{body}\n\n</details>")
}

fn bullets(items: &[String]) -> String {
    let mut lines: Vec<String> = items
        .iter()
        .take(LIST_LIMIT)
        .map(|item| format!("- {item}"))
        .collect();
    if items.len() > LIST_LIMIT {
        lines.push(format!("- and {} more", items.len() - LIST_LIMIT));
    }
    lines.join("\n")
}

fn plural(count: usize, noun: &str) -> String {
    let count_text = number(count as u64);
    if count == 1 {
        format!("{count_text} {noun}")
    } else {
        format!("{count_text} {noun}s")
    }
}

/// `1,234`.
fn number(value: u64) -> String {
    let digits = value.to_string();
    let mut text = String::new();
    for (index, digit) in digits.chars().enumerate() {
        if index > 0 && (digits.len() - index).is_multiple_of(3) {
            text.push(',');
        }
        text.push(digit);
    }
    text
}

/// `+12` or `-12`.
fn change(now: u64, before: u64) -> String {
    let sign = if now >= before { '+' } else { '-' };
    format!("{sign}{}", number(now.abs_diff(before)))
}

/// `1,234 (+12)`; the bare number without a base or when nothing changed.
fn with_change(now: u64, before: Option<u64>) -> String {
    match before {
        Some(before) if before != now => format!("{} ({})", number(now), change(now, before)),
        _ => number(now),
    }
}

fn seconds(nanos: u64) -> String {
    format!("{:.2} s", nanos as f64 / 1e9)
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    fn record(case: &str, outcome: Outcome, steps: u64) -> Record {
        Record {
            case: case.to_owned(),
            direction: Direction::ASubsumesB,
            expected: None,
            outcome,
            steps,
            nanos: 1_000_000,
        }
    }

    fn no() -> Outcome {
        no_with(Confirmation::Confirmed)
    }

    fn no_with(confirmation: Confirmation) -> Outcome {
        Outcome::No {
            counterexample: json!(0),
            confirmation,
        }
    }

    fn unknown() -> Outcome {
        Outcome::Unknown {
            reason: "budget".to_owned(),
            detail: "the check ran out of its work budget".to_owned(),
        }
    }

    #[test]
    fn without_a_base_the_comment_only_tallies() {
        let head = [
            record("one/a", Outcome::Yes, 3),
            record("one/b", unknown(), 0),
            record("two/a", no(), 5),
        ];
        let comparison = compare(&head, None, false);
        assert_eq!(comparison.lost, 0);
        let comment = comparison.comment;
        assert!(comment.contains("There are no results of the base branch"));
        assert!(comment.contains("| `one` | 2 | 1 | 0 | 1 | 0 | 0 |"));
        assert!(comment.contains("| `two` | 1 | 0 | 1 | 0 | 0 | 0 |"));
        assert!(comment.contains("| **total** | 3 | 1 | 1 | 1 | 0 | 0 |"));
        assert!(comment.contains("took 8 steps in total"));
        assert!(comment.contains("| `budget` | 1 |"));
        assert!(comment.contains("A validator confirms 1 of 1 counterexample."));
    }

    #[test]
    fn a_run_without_a_no_says_nothing_of_counterexamples() {
        let comment = compare(&[record("one/a", Outcome::Yes, 3)], None, false).comment;
        assert!(!comment.contains("counterexample"), "{comment}");
    }

    #[test]
    fn a_counterexample_that_is_none_is_a_wrong_verdict() {
        let head = [
            record("one/a", no(), 1),
            record("one/b", no_with(Confirmation::RejectedByNarrow), 1),
            record("one/c", no_with(Confirmation::AcceptedByWide), 1),
        ];
        let comment = compare(&head, None, false).comment;
        assert!(comment.contains("A validator confirms 1 of 3 counterexamples."));
        assert!(comment.contains(
            "### :x: 2 wrong verdicts\n\n\
             - `one/b` a_subsumes_b: No, and `b` rejects the counterexample `0`\n\
             - `one/c` a_subsumes_b: No, and `a` accepts the counterexample `0`"
        ));
        assert!(comment.contains("| **total** | 3 | 0 | 3 | 0 | 2 | 0 |"));
    }

    #[test]
    fn a_counterexample_that_was_not_checked_is_named_with_the_reason() {
        let unchecked = Confirmation::NotChecked("the validator does not take a schema".to_owned());
        let head = [
            record("one/a", no(), 1),
            record("one/b", no_with(unchecked), 1),
        ];
        let comment = compare(&head, None, false).comment;
        assert!(comment.contains("A validator confirms 1 of 2 counterexamples."));
        assert!(comment.contains("<summary>1 counterexample not checked</summary>"));
        assert!(comment.contains("- `one/b` a_subsumes_b: the validator does not take a schema"));
        // It is no wrong verdict.
        assert!(comment.contains("| **total** | 2 | 0 | 2 | 0 | 0 | 0 |"));
        assert!(!comment.contains(":x:"), "{comment}");
    }

    #[test]
    fn a_check_that_the_base_decided_is_lost_when_it_is_unknown_now() {
        let base = [record("one/a", Outcome::Yes, 3), record("one/b", no(), 4)];
        let head = [record("one/a", unknown(), 3), record("one/b", no(), 4)];
        let base = Base {
            records: &base,
            label: "abc1234",
        };

        let refused = compare(&head, Some(&base), false);
        assert_eq!(refused.lost, 1);
        assert!(refused.comment.contains("### :x: 1 check lost to Unknown"));
        assert!(
            refused
                .comment
                .contains("add the label `allow-lost-verdicts`")
        );
        assert!(
            refused
                .comment
                .contains("- `one/a` a_subsumes_b: Yes to Unknown (budget)")
        );
        assert!(
            refused
                .comment
                .contains("| `one` | 2 | 0 (-1) | 1 | 1 (+1) | 0 | 0 |")
        );

        let accepted = compare(&head, Some(&base), true);
        assert_eq!(accepted.lost, 1);
        assert!(
            accepted
                .comment
                .contains("### :warning: 1 check lost to Unknown")
        );
        assert!(
            accepted
                .comment
                .contains("The label `allow-lost-verdicts` accepts them.")
        );
    }

    #[test]
    fn newly_decided_and_flipped_checks_are_listed_and_lose_nothing() {
        let base = [
            record("one/a", unknown(), 0),
            record("one/b", Outcome::Yes, 2),
        ];
        let head = [record("one/a", Outcome::Yes, 9), record("one/b", no(), 2)];
        let base = Base {
            records: &base,
            label: "abc1234",
        };
        let comparison = compare(&head, Some(&base), false);
        assert_eq!(comparison.lost, 0);
        let comment = comparison.comment;
        assert!(comment.contains("Compared with `abc1234` on the base branch."));
        assert!(comment.contains(":white_check_mark: 1 check newly decided"));
        assert!(comment.contains("- `one/a` a_subsumes_b: Unknown (budget) to Yes"));
        assert!(comment.contains(":warning: 1 check changed between Yes and No"));
        assert!(comment.contains("1 check with a different number of steps"));
        assert!(comment.contains("| `one/a` a_subsumes_b | 0 | 9 | +9 |"));
        assert!(comment.contains("took 11 (+9) steps in total"));
    }

    #[test]
    fn a_wrong_verdict_and_an_error_are_named() {
        let mut wrong = record("one/a", no(), 1);
        wrong.expected = Some(true);
        let error = record(
            "one/b",
            Outcome::Error {
                message: "schema A is neither an object nor a boolean".to_owned(),
            },
            0,
        );
        let comment = compare(&[wrong, error], None, false).comment;
        assert!(comment.contains(
            "### :x: 1 wrong verdict\n\n- `one/a` a_subsumes_b: No, and the corpus says Yes"
        ));
        assert!(
            comment
                .contains("### :x: 1 error\n\n- `one/b` a_subsumes_b: Error (schema A is neither")
        );
        assert!(comment.contains("| **total** | 2 | 0 | 1 | 0 | 1 | 1 |"));
    }

    #[test]
    fn checks_in_only_one_run_are_counted_not_compared() {
        let base = [
            record("one/a", Outcome::Yes, 1),
            record("gone/a", Outcome::Yes, 1),
        ];
        let head = [
            record("one/a", Outcome::Yes, 1),
            record("new/a", unknown(), 0),
        ];
        let base = Base {
            records: &base,
            label: "abc1234",
        };
        let comparison = compare(&head, Some(&base), false);
        assert_eq!(comparison.lost, 0);
        assert!(
            comparison
                .comment
                .contains("1 only in this run, 1 only in the base.")
        );
    }

    #[test]
    fn long_lists_are_cut() {
        let items: Vec<String> = (0..LIST_LIMIT + 2).map(|index| index.to_string()).collect();
        let list = bullets(&items);
        assert_eq!(list.lines().count(), LIST_LIMIT + 1);
        assert!(list.ends_with("- and 2 more"));
    }

    #[test]
    fn numbers_get_thousands_separators() {
        assert_eq!(number(0), "0");
        assert_eq!(number(999), "999");
        assert_eq!(number(1000), "1,000");
        assert_eq!(number(29_228), "29,228");
        assert_eq!(number(1_234_567), "1,234,567");
        assert_eq!(with_change(1200, Some(1000)), "1,200 (+200)");
        assert_eq!(with_change(800, Some(1000)), "800 (-200)");
        assert_eq!(with_change(1000, Some(1000)), "1,000");
    }
}
