//! Focused source integration tests for the public bounded QM31 sampler.
//!
//! Scripted memoizing hash answers exercise literal transcript control flow;
//! they do not establish a random-oracle law or V8 verifier soundness.

use aspis_core::transcript::Transcript;
use std::cell::RefCell;
use std::collections::{BTreeMap, VecDeque};

#[derive(Default)]
struct State {
    answers: VecDeque<[u8; 32]>,
    table: BTreeMap<Vec<u8>, [u8; 32]>,
    calls: Vec<Vec<u8>>,
}

thread_local! {
    static STATE: RefCell<State> = RefCell::new(State::default());
}

fn reset(answers: Vec<[u8; 32]>) {
    STATE.with(|state| {
        *state.borrow_mut() = State {
            answers: answers.into(),
            ..State::default()
        };
    });
}

fn oracle(parts: &[&[u8]]) -> [u8; 32] {
    let input = parts.concat();
    STATE.with(|cell| {
        let mut state = cell.borrow_mut();
        state.calls.push(input.clone());
        if let Some(answer) = state.table.get(&input) {
            return *answer;
        }
        let answer = state
            .answers
            .pop_front()
            .expect("unexpected fresh source hash call");
        state.table.insert(input, answer);
        answer
    })
}

fn block(words: [u32; 8]) -> [u8; 32] {
    let mut bytes = [0; 32];
    for (index, word) in words.iter().enumerate() {
        bytes[4 * index..4 * index + 4].copy_from_slice(&word.to_le_bytes());
    }
    bytes
}

fn limbs(transcript: &mut Transcript) -> [u32; 4] {
    let value = transcript.challenge_qm31().unwrap();
    [value.c0.a.0, value.c0.b.0, value.c1.a.0, value.c1.b.0]
}

fn call_count() -> usize {
    STATE.with(|state| state.borrow().calls.len())
}

const P: u32 = (1_u32 << 31) - 1;

#[test]
fn ordinary_alpha_accepts_zero_and_ignores_high_bits() {
    reset(vec![
        block([
            1 << 31,
            (1 << 31) + 1,
            (1 << 31) + 2,
            (1 << 31) + 3,
            0,
            0,
            0,
            0,
        ]),
        [9; 32],
    ]);
    let mut transcript = Transcript::new(oracle);
    assert_eq!(limbs(&mut transcript), [0, 1, 2, 3]);
    assert_eq!(call_count(), 2);
    assert_eq!(transcript.diagnostic_state(), [9; 32]);
}

#[test]
fn sentinel_is_rejected_not_folded_to_zero() {
    reset(vec![block([P, u32::MAX, 4, 5, 6, 7, 8, 9]), [9; 32]]);
    assert_eq!(limbs(&mut Transcript::new(oracle)), [4, 5, 6, 7]);
}

#[test]
fn exact_last_word_success_makes_no_extra_squeeze() {
    reset(vec![block([P, P, P, P, 1, 2, 3, 4]), [9; 32]]);
    assert_eq!(limbs(&mut Transcript::new(oracle)), [1, 2, 3, 4]);
    assert_eq!(call_count(), 2);
}

#[test]
fn per_limb_eight_retries_can_use_four_pairs() {
    let mut answers = Vec::new();
    for answer in 1_u8..=4 {
        answers.push(block([P, P, P, P, P, P, P, u32::from(answer)]));
        answers.push([answer; 32]);
    }
    reset(answers);
    let mut transcript = Transcript::new(oracle);
    assert_eq!(limbs(&mut transcript), [1, 2, 3, 4]);
    assert_eq!(call_count(), 8);
    assert_eq!(transcript.diagnostic_state(), [4; 32]);
}

#[test]
fn exhausted_first_limb_still_advances() {
    reset(vec![block([P; 8]), [9; 32]]);
    let mut transcript = Transcript::new(oracle);
    assert!(transcript.challenge_qm31().is_err());
    assert_eq!(call_count(), 2);
    assert_eq!(transcript.diagnostic_state(), [9; 32]);
}

#[test]
fn source_output_and_advance_have_literal_distinct_keys() {
    reset(vec![block([0; 8]), [9; 32]]);
    let _ = limbs(&mut Transcript::new(oracle));
    STATE.with(|state| {
        let state = state.borrow();
        let mut key = vec![0; 32];
        key.push(1);
        assert_eq!(state.calls[0], key);
        key[32] = 2;
        assert_eq!(state.calls[1], key);
    });
}

#[test]
fn adversary_prequery_is_cached_not_resampled() {
    reset(vec![block([7; 8]), [9; 32]]);
    let mut key = vec![0; 32];
    key.push(1);
    let answer = oracle(&[&key]);
    assert_eq!(answer, block([7; 8]));
    assert_eq!(limbs(&mut Transcript::new(oracle)), [7; 4]);
    assert_eq!(call_count(), 3);
    STATE.with(|state| assert!(state.borrow().answers.is_empty()));
}

#[test]
fn repeated_advance_state_reuses_cached_output_block() {
    reset(vec![block([P, P, P, P, P, P, P, 2]), [0; 32]]);
    assert_eq!(limbs(&mut Transcript::new(oracle)), [2; 4]);
    assert_eq!(call_count(), 8);
    STATE.with(|state| assert_eq!(state.borrow().table.len(), 2));
}
