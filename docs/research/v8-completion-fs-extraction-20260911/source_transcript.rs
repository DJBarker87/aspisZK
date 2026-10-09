//! Executes the actual pinned core source, not a Python transcription.
//! Controlled full-answer oracles test deterministic behavior, not ROM rates.
#![allow(dead_code)]
extern crate alloc;
#[path = "../../../crates/aspis-core/src/field.rs"] mod field;
#[path = "../../../crates/aspis-core/src/circle.rs"] mod circle;
#[path = "../../../crates/aspis-core/src/transcript.rs"] mod transcript;
#[path = "../../../crates/aspis-core/src/statement_sumcheck.rs"] mod statement_sumcheck;
#[path = "../../../crates/aspis-core/src/state_only_sumcheck.rs"] mod state_only_sumcheck;
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
    semantic_controls();
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
    // Early-root subtrace, with C2 chosen only after both actual challenge
    // samplers return. A zero oracle exposes the cache/fresh distinction.
    reset(1);
    let mut early=Transcript::new(hash);
    let c1_fixed_cut=log().len();
    early.absorb(transcript::label::ROOT,&[19;26]);
    let c1_absorbed=log().len();
    let lambda=early.challenge_qm31().unwrap();
    let chi=early.challenge_qm31().unwrap();
    let c2=[(lambda.c0.a.0 ^ chi.c0.a.0) as u8;26];
    let c2_fixed_cut=log().len();
    early.absorb(transcript::label::SECOND_PHASE_ROOT,&c2);
    let c2_absorbed=log().len();
    assert_eq!((c1_fixed_cut,c2_fixed_cut),(0,5));
    assert_eq!((c1_absorbed,c2_absorbed),(1,6));
    assert_eq!(log().iter().map(|e|!e.2).collect::<Vec<_>>(),vec![true,true,true,false,false,true]);
    reset(1);
    let mut building=Transcript::new(hash);
    building.absorb(transcript::label::ROOT,&[0;26]);
    building.challenge_qm31().unwrap();building.challenge_qm31().unwrap();
    let built_answer=hash(&[&[99]]); // A model builder call, not a Merkle leaf encoding.
    let built_cut=log().len();
    building.absorb(transcript::label::SECOND_PHASE_ROOT,&built_answer[..26]);
    assert_eq!((built_cut,log().len()),(6,7));
    reset(1);
    let root1=hash(&[&[98]]);
    let first_builder_cut=log().len();
    let mut both=Transcript::new(hash);
    both.absorb(transcript::label::ROOT,&root1[..26]);
    both.challenge_qm31().unwrap();both.challenge_qm31().unwrap();
    let root2=hash(&[&[99]]);
    let second_builder_cut=log().len();
    both.absorb(transcript::label::SECOND_PHASE_ROOT,&root2[..26]);
    assert_eq!((first_builder_cut,second_builder_cut,log().len()),(1,7,8));
    assert_eq!(log().iter().filter(|e|!e.2).count(),6);
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

fn semantic_controls() {
    use field::{M31,CM31,QM31 as K};
    let scalar=|n:u32| K { c0:CM31 { a:M31(n), b:M31::ZERO }, c1:CM31::ZERO };
    let qvalue=|n:u32| K {c0:CM31 {a:M31(n%field::P),b:M31((field::P-1-n%field::P)%field::P)},
        c1:CM31 {a:M31((u64::from(n)*13%u64::from(field::P)) as u32),b:M31(((u64::from(n)*u64::from(n)+7)%u64::from(field::P)) as u32)}};
    let execute=|w:&[K;697],coins:[K;10]| {
        let mut claim=w[0];
        for r in 0..10 {
            let sent=&w[1+27*r..1+27*(r+1)];
            let mut poly=[K::ZERO;28];poly[0]=sent[0];poly[2..].copy_from_slice(&sent[1..]);
            poly[1]=claim.sub(poly[0].add(poly[0]).add(poly[2..].iter().copied().fold(K::ZERO,|a,b|a.add(b))));
            claim=state_only_sumcheck::evaluate_state_only_polynomial(&poly,coins[r]);
        }
        (claim, std::array::from_fn::<_,84,_>(|i|w[271+(i/28)*29+i%28]))
    };
    for seed in 0..32 {
        let word=std::array::from_fn(|i|scalar(i as u32*i as u32+seed*17+9));
        let coins=std::array::from_fn(|r|scalar(r as u32*11+seed));
        let result=execute(&word,coins);
        let mut changed=word;
        for i in 358..697 {changed[i]=changed[i].add(K::ONE);}
        for i in [299,328,357] {changed[i]=changed[i].add(K::ONE);}
        assert_eq!(result,execute(&changed,coins));
        assert_eq!(result.0,scalar(result.0.c0.a.0));
        println!("SEMANTIC {seed} {}",result.0.c0.a.0);
        let qw=std::array::from_fn(|i|qvalue(i as u32*i as u32+seed*17+9));
        let qc=std::array::from_fn(|i|qvalue(i as u32*11+seed));
        let q=execute(&qw,qc).0;
        println!("SEMANTIC_Q {seed} {} {} {} {}",q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0);
    }
}
