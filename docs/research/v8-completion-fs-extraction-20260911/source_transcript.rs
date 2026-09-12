//! Executes the actual pinned core source, not a Python transcription.
//! Controlled full-answer oracles test deterministic behavior, not ROM rates.
#![allow(dead_code)]
extern crate alloc;
#[path = "../../../crates/aspis-core/src/field.rs"] mod field;
#[path = "../../../crates/aspis-core/src/circle.rs"] mod circle;
#[path = "../../../crates/aspis-core/src/transcript.rs"] mod transcript;
// Only unused legacy KAT functions require this constant. The runner verifies
// its literal definition against sumcheck.rs; no sumcheck code is executed.
mod sumcheck { pub const SUMCHECK_BYTES: usize = 7 * 16; }
use std::{cell::RefCell, collections::BTreeMap};
use transcript::Transcript;
#[derive(Default)]
struct Recorder {
    cache: BTreeMap<Vec<u8>, [u8; 32]>,
    log: Vec<(Vec<u8>, [u8; 32], bool)>,
    mode: u8,
}
thread_local! { static ORACLE: RefCell<Recorder> = RefCell::new(Recorder::default()); }
fn reset(mode: u8) { ORACLE.with(|r| *r.borrow_mut() = Recorder { mode, ..Default::default() }); }
fn hash(parts: &[&[u8]]) -> [u8; 32] {
    let input = parts.concat();
    ORACLE.with(|r| {
        let mut r = r.borrow_mut();
        let cached = r.cache.get(&input).copied();
        let answer = cached.unwrap_or_else(|| {
            if r.mode == 1 { [0; 32] } else if r.mode == 2 { [255; 32] } else {
                let mut out = [0u8; 32];
                for i in 0..8 { out[4*i..4*i+4].copy_from_slice(&((r.cache.len()*8+i+1) as u32).to_le_bytes()); }
                out
            }
        });
        r.cache.insert(input.clone(), answer);
        r.log.push((input, answer, cached.is_some()));
        answer
    })
}
fn log() -> Vec<(Vec<u8>, [u8; 32], bool)> { ORACLE.with(|r| r.borrow().log.clone()) }
fn main() {
    // Packed/zero-copy branches and two-piece absorption are byte-identical.
    for len in [0, 1, 158, 159, 16384] {
        reset(0);
        let data = vec![17; len];
        let mut a = Transcript::new(hash);
        a.absorb(73, &data);
        let mut expected = vec![0; 32]; expected.extend([0,73]); expected.extend(&data);
        assert_eq!(log()[0].0, expected);
        let mut b = Transcript::new(hash);
        b.absorb_two(73, &data[..len/2], &data[len/2..]);
        assert_eq!(a.diagnostic_state(), b.diagnostic_state());
        assert!(log()[1].2); // Different slice partition, same cached input.
    }
    reset(0);
    let mut t = Transcript::new(hash);
    t.absorb(3, &[19;26]);
    let before = t.diagnostic_state();
    let answer = t.squeeze_block();
    let calls = log();
    assert_eq!(calls[1].0, [&before[..], &[1]].concat());
    assert_eq!(calls[2].0, [&before[..], &[2]].concat());
    assert_eq!(answer, calls[1].1);
    assert_eq!(t.diagnostic_state(), calls[2].1);
    // Restoring the same prefix reuses full answers, not independent draws.
    let mut restored = Transcript::new(hash);
    restored.absorb(3, &[19;26]);
    assert_eq!(restored.squeeze_block(), answer);
    assert!(log()[3..].iter().all(|e| e.2));
    // Actual bounded samplers must retain failure even under degenerate oracles.
    reset(1);
    assert!(Transcript::new(hash).challenge_nonzero_qm31().is_err());
    assert_eq!(log().len(), 6); // Three candidates, squeeze + advance each.
    assert!(log().iter().skip(2).all(|e| e.2));
    reset(2);
    assert!(Transcript::new(hash).challenge_qm31().is_err());
    assert_eq!(log().len(), 2); // Eight rejected words for first limb.
    reset(1);
    assert!(matches!(Transcript::new(hash).challenge_queries_without_replacement(22, 1<<18, 64),
        Err(transcript::QuerySampleError::DrawLimitExhausted { accepted: 1, max_draws: 64 })));
    assert_eq!(log().len(), 16);
    reset(0);
    let queries = Transcript::new(hash).challenge_queries_without_replacement(22, 1<<18, 64).unwrap();
    assert_eq!(queries.len(),22);
    assert!(queries.iter().enumerate().all(|(i,q)| queries[..i].iter().all(|other| other != q)));
    reset(0);
    assert!(Transcript::new(hash).challenge_queries_without_replacement(0,1<<18,64).unwrap().is_empty());
    assert!(log().is_empty());
    assert!(Transcript::new(hash).challenge_queries_without_replacement(22,3,64).is_err());
    assert!(log().is_empty());
    println!("PASS actual-source absorption, chronological squeeze/advance, restored cache, bounded QM31/nonzero/query samplers; deterministic controls only");
}
