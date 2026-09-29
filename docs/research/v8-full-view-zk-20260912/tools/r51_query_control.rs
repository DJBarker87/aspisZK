//! Actual source framing/first-hit checks, using a memoized SCRIPTED oracle.
//! These are deterministic control tests, not a random-oracle probability test.
use aspis_core::transcript::{ChallengeSampleExhausted, QuerySampleError, Transcript};
use std::cell::RefCell;
use std::collections::BTreeMap;

#[derive(Clone, Copy)]
enum Mode { Advance, Freeze, Reject }
#[derive(Clone)]
struct Read { input: Vec<u8>, output: [u8;32], hit: bool }
struct Oracle { mode: Mode, table: BTreeMap<Vec<u8>,[u8;32]>, reads: Vec<Read> }
thread_local! {static ORACLE: RefCell<Oracle> = RefCell::new(Oracle {
    mode:Mode::Advance,table:BTreeMap::new(),reads:Vec::new()});}
fn backend(parts:&[&[u8]]) -> [u8;32] {
    let input:Vec<u8> = parts.iter().flat_map(|p|p.iter().copied()).collect();
    ORACLE.with(|o| {
        let mut o=o.borrow_mut();let hit=o.table.contains_key(&input);
        let output=if let Some(&answer)=o.table.get(&input) { answer } else {
            let mut answer=[0;32];
            if input.len()==33 && input[32]==1 {
                let counter=u32::from_le_bytes(input[..4].try_into().unwrap());
                for j in 0..8 {
                    let word=match o.mode {Mode::Reject=>0x7fff_ffff,
                        Mode::Freeze=>0,Mode::Advance=>counter*8+j};
                    answer[j as usize*4..j as usize*4+4].copy_from_slice(&word.to_le_bytes());
                }
            } else if input.len()==33 && input[32]==2 {
                answer.copy_from_slice(&input[..32]);
                if matches!(o.mode,Mode::Advance) {
                    let counter=u32::from_le_bytes(input[..4].try_into().unwrap())+1;
                    answer[..4].copy_from_slice(&counter.to_le_bytes());
                }
            } else {
                // A fixed memoized answer for each new absorb/grind address.
                answer[..4].copy_from_slice(&(o.table.len() as u32+1000).to_le_bytes());
            }
            o.table.insert(input.clone(),answer);answer
        };
        o.reads.push(Read{input,output,hit});output
    })
}
fn reset(mode:Mode)->Transcript {
    ORACLE.with(|o|*o.borrow_mut()=Oracle{mode,table:BTreeMap::new(),reads:Vec::new()});
    Transcript::new(backend)
}
fn reads()->Vec<Read> { ORACLE.with(|o|o.borrow().reads.clone()) }
fn frame(state:[u8;32],domain:u8)->Vec<u8> { [state.as_slice(),&[domain]].concat() }
fn check_pairs(log:&[Read],mut state:[u8;32]) {
    assert_eq!(log.len()%2,0);
    for pair in log.chunks_exact(2) {
        assert_eq!(pair[0].input,frame(state,1));
        assert_eq!(pair[1].input,frame(state,2));
        assert_ne!(pair[0].input,pair[1].input);
        state=pair[1].output;
    }
}
fn main() {
    let mut t=reset(Mode::Advance);
    for _ in 0..64 {let old=t.diagnostic_state();let out=t.squeeze_block();
        let log=reads();let pair=&log[log.len()-2..];check_pairs(pair,old);
        assert_eq!(out,pair[0].output);assert_eq!(t.diagnostic_state(),pair[1].output);
        assert!(pair.iter().all(|r|!r.hit));}
    check_pairs(&reads(),[0;32]);

    // A repeated state repeats both cells. Domain separation cannot prevent it.
    let mut t=reset(Mode::Freeze);let a=t.squeeze_block();let b=t.squeeze_block();
    assert_eq!(a,b);assert_eq!(t.diagnostic_state(),[0;32]);
    let log=reads();check_pairs(&log,[0;32]);
    assert!(!log[0].hit&&!log[1].hit&&log[2].hit&&log[3].hit);
    // External reads can hit either address even with no prior squeeze step.
    for domain in [1,2] {let mut t=reset(Mode::Advance);
        let addr=frame([0;32],domain);let answer=backend(&[&addr]);t.squeeze_block();
        let log=reads();assert_eq!(log.len(),3);
        assert!(log[domain as usize].hit);assert_eq!(log[domain as usize].output,answer);
        assert!(!log[3-domain as usize].hit);check_pairs(&log[1..],[0;32]);}

    // Packed and hashv absorb paths, and split framing, address the same bytes.
    let mut absorb_cases=0;
    for len in [0,1,158,159,1024] {for label in [0,1,255] {
        let t=reset(Mode::Advance);let mut left=t.clone();let mut right=t;
        let data:Vec<u8>=(0..len).map(|i|(i%256)as u8).collect();
        left.absorb(label,&data);right.absorb_two(label,&data[..len/2],&data[len/2..]);
        let log=reads();let expected=[&[0u8;32][..],&[0,label],data.as_slice()].concat();
        assert_eq!(log.len(),2);assert_eq!(log[0].input,expected);assert_eq!(log[1].input,expected);
        assert!(!log[0].hit&&log[1].hit);assert_eq!(left.diagnostic_state(),right.diagnostic_state());
        assert_ne!(expected.len(),33);absorb_cases+=1;
    }}
    // Failure observations and memoized reads remain part of the experiment.
    let mut t=reset(Mode::Reject);
    assert_eq!(t.challenge_qm31(),Err(ChallengeSampleExhausted));
    assert_eq!(reads().len(),2);check_pairs(&reads(),[0;32]);
    assert_eq!(t.challenge_qm31(),Err(ChallengeSampleExhausted));
    assert!(reads()[2..].iter().all(|r|r.hit));
    let mut t=reset(Mode::Freeze);
    assert_eq!(t.challenge_queries_without_replacement(22,1<<18,64),
        Err(QuerySampleError::DrawLimitExhausted{accepted:1,max_draws:64}));
    let log=reads();assert_eq!(log.len(),16);check_pairs(&log,[0;32]);
    assert!(log[2..].iter().all(|r|r.hit));
    println!("R51_DUPLEX_CONTROL advancing_pairs=64 repeated_state_controls=1 prior_read_controls=2 absorb_equivalence_cases={absorb_cases} rejection_controls=2 repeated_failure_controls=1 actual_source=true memoized_script=true source_probability=false full_privacy=false");
}
