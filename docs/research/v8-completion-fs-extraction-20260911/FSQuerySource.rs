//! Exact source query-sampler controls, synthetic cached full-answer oracle.
//! Not a ROM distribution experiment and not a payment proof.
#![allow(dead_code)]
extern crate alloc;
#[path = "../../../crates/aspis-core/src/field.rs"] mod field;
#[path = "../../../crates/aspis-core/src/circle.rs"] mod circle;
#[path = "../../../crates/aspis-core/src/transcript.rs"] mod transcript;
mod sumcheck { pub const SUMCHECK_BYTES: usize = 7*16; }
use std::{cell::RefCell, collections::BTreeMap};
#[derive(Default)]
struct Oracle {
    cache: BTreeMap<Vec<u8>, [u8;32]>,
    log: Vec<(Vec<u8>,[u8;32],bool)>,
    mode: u8,
    blocks: usize,
}
thread_local! { static ORACLE: RefCell<Oracle> = RefCell::new(Oracle::default()); }
fn reset(mode: u8) { ORACLE.with(|x| *x.borrow_mut() = Oracle {mode,..Default::default()}); }
fn hash(parts: &[&[u8]]) -> [u8;32] {
    let input=parts.concat();
    ORACLE.with(|state| {
        let mut state=state.borrow_mut();
        let cached=state.cache.get(&input).copied();
        let answer=if let Some(answer)=cached { answer } else if state.mode==3 { [0;32] }
        else if input.len()==33 && input[32]==1 {
            let mut block=[0u8;32];
            for lane in 0..8 {
                let ordinal=state.blocks*8+lane;
                let value=match state.mode {
                    1 if ordinal==21 => 0,
                    1 if ordinal==22 => 1,
                    1 if ordinal>=23 => ordinal-2,
                    2 if (21..63).contains(&ordinal) => 0,
                    2 if ordinal==63 => 21,
                    _ => ordinal,
                } as u32;
                // Exercise high unused bits: source masks, rather than rejecting them.
                block[4*lane..4*lane+4].copy_from_slice(&(value | 0xfffc0000).to_le_bytes());
            }
            state.blocks+=1;
            block
        } else { [64+state.cache.len() as u8;32] };
        state.cache.insert(input.clone(),answer);
        state.log.push((input,answer,cached.is_none()));
        answer
    })
}
fn main() {
    for (mode,expected_blocks) in [(0,3),(1,4),(2,8)] {
        reset(mode);
        let mut source=transcript::Transcript::new(hash);
        let result=source.challenge_queries_without_replacement(22,1<<18,64).unwrap();
        assert_eq!(result,(0..22).collect::<Vec<u32>>());
        ORACLE.with(|state| {
            let state=state.borrow();
            assert_eq!(state.blocks,expected_blocks);
            assert_eq!(state.log.len(),2*expected_blocks);
            let mut prior=[0u8;32];
            for pair in state.log.chunks_exact(2) {
                assert_eq!(pair[0].0,[prior.as_slice(),&[1]].concat());
                assert_eq!(pair[1].0,[prior.as_slice(),&[2]].concat());
                prior=pair[1].1;
            }
            assert_eq!(source.diagnostic_state(),prior);
        });
    }
    reset(3);
    let mut source=transcript::Transcript::new(hash);
    assert!(matches!(source.challenge_queries_without_replacement(22,1<<18,64),
        Err(transcript::QuerySampleError::DrawLimitExhausted {accepted:1,max_draws:64})));
    ORACLE.with(|state| {
        let state=state.borrow();
        assert_eq!(state.log.len(),16);
        assert_eq!(state.log.iter().filter(|x|x.2).count(),2);
    });
    let mut restored=transcript::Transcript::new(hash);
    assert!(restored.challenge_queries_without_replacement(22,1<<18,64).is_err());
    ORACLE.with(|state| {
        let state=state.borrow();
        assert_eq!(state.log.len(),32);
        assert!(state.log[16..].iter().all(|x|!x.2));
    });
    println!("PASS: ordinary3blocks; completion-at24 consumes4blocks; completion-at64 consumes8blocks; duplicate exhaustion; cached restoration; exact squeeze/advance inputs and final states; synthetic data only");
}
