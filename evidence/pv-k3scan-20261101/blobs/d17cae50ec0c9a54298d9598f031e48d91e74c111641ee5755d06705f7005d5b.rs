//! Operational sampler boundaries, not a random-oracle or SHA-256 security test.
//! A deterministic injected backend is permitted by Transcript's API. Freshness
//! therefore needs an explicit cryptographic good-event argument, not just an
//! appeal to the presence of a DOM_ADVANCE call.
use aspis_core::field::{CM31, M31, P, QM31};
use aspis_core::transcript::{CirclePointSampleError, Transcript};
use std::cell::RefCell;
use sha2::{Digest, Sha256};

#[derive(Default)]
struct Trace {
    calls: Vec<Vec<u8>>,
    mode: u8,
}
thread_local! { static TRACE: RefCell<Trace> = RefCell::new(Trace::default()); }

fn reset(mode: u8) {
    TRACE.with(|t| *t.borrow_mut() = Trace { calls: Vec::new(), mode });
}

fn scripted_hash(parts: &[&[u8]]) -> [u8; 32] {
    let input: Vec<u8> = parts.iter().flat_map(|x| x.iter().copied()).collect();
    assert_eq!(input.len(), 33, "these tests exercise squeezes/advances only");
    TRACE.with(|t| {
        let mut t = t.borrow_mut();
        t.calls.push(input.clone());
        let mut out = [0u8; 32];
        match input[32] {
            1 => {
                let words = match t.mode {
                    // Accepted non-subfield parameter; repeated input, repeated output.
                    0 => [17, 18, 19, 20, 21, 22, 23, 24],
                    // Seven rejected words before each accepted limb; four blocks.
                    1 => [P, P, P, P, P, P, P, 17 + u32::from(input[0])],
                    // Every QM31 value is zero, hence rejected by the OOD policy.
                    2 => [0; 8],
                    // The first limb exhausts all eight allowed attempts.
                    3 => [P; 8],
                    _ => unreachable!(),
                };
                for (slot, word) in out.chunks_exact_mut(4).zip(words) {
                    slot.copy_from_slice(&word.to_le_bytes());
                }
            }
            2 => {
                // Mode zero deliberately cycles to the initial state. Other modes
                // use a distinct, deterministic next state for each block.
                if t.mode != 0 { out[0] = input[0].checked_add(1).unwrap(); }
            }
            _ => panic!("unexpected domain"),
        }
        out
    })
}

fn squeezes() -> Vec<Vec<u8>> {
    TRACE.with(|t| t.borrow().calls.iter().filter(|x| x[32] == 1).cloned().collect())
}

fn logged_sha256(parts: &[&[u8]]) -> [u8; 32] {
    let input: Vec<u8> = parts.iter().flat_map(|x| x.iter().copied()).collect();
    TRACE.with(|t| t.borrow_mut().calls.push(input.clone()));
    Sha256::digest(&input).into()
}

#[test]
fn public_next_squeeze_can_be_prequeried_without_a_collision() {
    reset(0);
    let mut next_input = [0u8; 33];
    next_input[32] = 1;
    let _prior_answer = logged_sha256(&[&next_input]);
    let mut t = Transcript::new(logged_sha256);
    t.challenge_qm31().unwrap();
    let inputs = squeezes();
    assert_eq!(inputs.len(), 2);
    assert_eq!(inputs[0], inputs[1]);
    TRACE.with(|t| assert_eq!(t.borrow().calls.len(), 3));
}

#[test]
fn advancing_state_does_not_unconditionally_imply_fresh_inputs() {
    reset(0);
    let mut t = Transcript::new(scripted_hash);
    let first = t.challenge_qm31().unwrap();
    for _ in 0..5 { assert_eq!(t.challenge_qm31().unwrap(), first); }
    let inputs = squeezes();
    assert_eq!(inputs.len(), 6);
    assert!(inputs.iter().all(|x| x == &inputs[0]));
    assert_eq!(t.diagnostic_state(), [0; 32]);
    TRACE.with(|t| assert_eq!(t.borrow().calls.len(), 12));
}

#[test]
fn maximal_successful_limb_retries_consume_four_blocks() {
    reset(1);
    let mut t = Transcript::new(scripted_hash);
    assert_eq!(t.challenge_qm31().unwrap(), QM31 {
        c0: CM31::new(M31(17), M31(18)),
        c1: CM31::new(M31(19), M31(20)),
    });
    let inputs = squeezes();
    assert_eq!(inputs.len(), 4);
    for (i, input) in inputs.iter().enumerate() { assert_eq!(input[0], i as u8); }
    TRACE.with(|t| assert_eq!(t.borrow().calls.len(), 8));
}

#[test]
fn outer_circle_exhaustion_and_inner_limb_exhaustion_stay_distinct() {
    reset(2);
    let mut t = Transcript::new(scripted_hash);
    assert_eq!(t.challenge_secure_circle_point(), Err(CirclePointSampleError::ParameterSampleExhausted));
    assert_eq!(squeezes().len(), 3);
    reset(3);
    let mut t = Transcript::new(scripted_hash);
    assert_eq!(t.challenge_secure_circle_point(), Err(CirclePointSampleError::ChallengeSampleExhausted));
    assert_eq!(squeezes().len(), 1);
}

#[test]
fn core_circle_sampler_does_not_enforce_distinct_successive_points() {
    reset(0);
    let mut t = Transcript::new(scripted_hash);
    let first = t.challenge_secure_circle_point().unwrap();
    assert_eq!(t.challenge_secure_circle_point().unwrap(), first);
    assert_eq!(squeezes().len(), 2);
}
