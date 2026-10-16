//! Test-only source overlay: exact old/new production begin declarations run
//! against the same instrumented interfaces. This checks Rust Result/error and
//! call-order behavior, not reachability of injected failures in production.
#![allow(dead_code, private_bounds, private_interfaces)]
use std::{cell::RefCell, marker::PhantomData, rc::Rc};

include!("error.rs");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct QM31(u8);
impl QM31 { const ZERO: Self = Self(0); }

trait Digest32 {}
struct TestDigest;
impl Digest32 for TestDigest {}

#[derive(Debug, PartialEq, Eq)]
struct Challenges {
    lambda: QM31,
    chi: QM31,
    theta: QM31,
    zc: [QM31; 10],
    mu: QM31,
    eta: QM31,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Event { Lookup(u8), Semantic(u8), Advance(u8) }

#[derive(Clone, Copy, Debug)]
enum Failure { Lookup(u8), Semantic(u8) }

struct Prefix<'a> {
    failure: Option<Failure>,
    events: Rc<RefCell<Vec<Event>>>,
    marker: PhantomData<&'a ()>,
}

struct ValidatedRecord { row: u8 }

impl Prefix<'_> {
    fn validated_record(&self, row: u8) -> Result<ValidatedRecord, Error> {
        self.events.borrow_mut().push(Event::Lookup(row));
        if matches!(self.failure, Some(Failure::Lookup(r)) if r == row) {
            return Err(Error::InvalidRow);
        }
        Ok(ValidatedRecord { row })
    }
}

struct SemanticTranscript<H: Digest32> {
    failure: Option<Failure>,
    events: Rc<RefCell<Vec<Event>>>,
    next_row: u8,
    state_prefix: Vec<u8>,
    marker: PhantomData<H>,
}

impl<H: Digest32> SemanticTranscript<H> {
    fn semantic_validated(&mut self, record: ValidatedRecord) -> Result<QM31, Error> {
        let row = record.row;
        self.events.borrow_mut().push(Event::Semantic(row));
        // Concrete production Error constructor, deliberately injected at the
        // interface boundary before any state advance. No production hook.
        if matches!(self.failure, Some(Failure::Semantic(r)) if r == row) {
            return Err(Error::RowOrder { expected: row, actual: row + 1 });
        }
        assert_eq!(row, self.next_row);
        self.next_row += 1;
        self.state_prefix.push(row);
        self.events.borrow_mut().push(Event::Advance(row));
        Ok(QM31(row + 1))
    }
}

mod old { use super::*; include!("old_begin.rs"); }
mod new { use super::*; include!("new_begin.rs"); }

type Outcome = (Result<Challenges, Error>, Vec<Event>, u8, Vec<u8>);

fn execute(new: bool, failure: Option<Failure>) -> Outcome {
    let events = Rc::new(RefCell::new(Vec::new()));
    let prefix = Prefix { failure, events: events.clone(), marker: PhantomData };
    let mut transcript = SemanticTranscript::<TestDigest> {
        failure, events: events.clone(), next_row: 0,
        state_prefix: Vec::new(), marker: PhantomData,
    };
    let result = if new { new::begin(&prefix, &mut transcript) }
        else { old::begin(&prefix, &mut transcript) };
    let calls = events.borrow().clone();
    (result, calls, transcript.next_row, transcript.state_prefix)
}

#[test]
fn exact_begin_bodies_preserve_each_zc_failure_error_and_prefix() {
    for row in 3..=12 {
        for failure in [Failure::Lookup(row), Failure::Semantic(row)] {
            let before = execute(false, Some(failure));
            let after = execute(true, Some(failure));
            assert_eq!(after, before, "failure {failure:?}");
            let mut expected_events = Vec::new();
            for prior in 0..row {
                expected_events.extend([Event::Lookup(prior), Event::Semantic(prior), Event::Advance(prior)]);
            }
            expected_events.push(Event::Lookup(row));
            let expected_error = match failure {
                Failure::Lookup(_) => Error::InvalidRow,
                Failure::Semantic(_) => {
                    expected_events.push(Event::Semantic(row));
                    Error::RowOrder { expected: row, actual: row + 1 }
                }
            };
            assert_eq!(after.0, Err(expected_error));
            assert_eq!(after.1, expected_events);
            assert_eq!(after.2, row);
            assert_eq!(after.3, (0..row).collect::<Vec<_>>());
            println!("failure {failure:?}: exact error, lookup/semantic/advance prefix and state prefix equal");
        }
    }
}

#[test]
fn exact_begin_bodies_preserve_success_challenges_and_all_fifteen_rows() {
    let before = execute(false, None);
    let after = execute(true, None);
    assert_eq!(after, before);
    assert_eq!(after.0, Ok(Challenges {
        lambda: QM31(1), chi: QM31(2), theta: QM31(3),
        zc: std::array::from_fn(|i| QM31(i as u8 + 4)),
        mu: QM31(14), eta: QM31(15),
    }));
    assert_eq!(after.2, 15);
    assert_eq!(after.3, (0..15).collect::<Vec<_>>());
    assert_eq!(after.1, (0..15).flat_map(|r| [Event::Lookup(r), Event::Semantic(r), Event::Advance(r)]).collect::<Vec<_>>());
}
