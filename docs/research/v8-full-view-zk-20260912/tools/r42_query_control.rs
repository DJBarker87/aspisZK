//! Source loop/control tests with a deliberately scripted (not random) hash backend.
use aspis_core::transcript::{QuerySampleError, Transcript};
use std::cell::RefCell;
#[derive(Default)]
struct Script { words: Vec<u32>, calls: Vec<(u8,usize)> }
thread_local! {static SCRIPT:RefCell<Script>=RefCell::new(Script::default());}
fn backend(parts:&[&[u8]])->[u8;32] {
    let bytes:Vec<u8>=parts.iter().flat_map(|p|p.iter().copied()).collect();
    assert_eq!(bytes.len(),33);let dom=bytes[32];
    let block=u64::from_le_bytes(bytes[..8].try_into().unwrap()) as usize;
    assert!(bytes[8..32].iter().all(|&b|b==0));
    SCRIPT.with(|s|{let mut s=s.borrow_mut();s.calls.push((dom,block));let mut out=[0;32];
        match dom {1=>{for j in 0..8 {out[4*j..4*j+4].copy_from_slice(&s.words[8*block+j].to_le_bytes());}},
            2=>out[..8].copy_from_slice(&((block+1)as u64).to_le_bytes()),_=>panic!("unexpected domain")};out})
}
fn setup(words:Vec<u32>)->Transcript {
    assert_eq!(words.len(),72);
    SCRIPT.with(|s|*s.borrow_mut()=Script{words,calls:Vec::new()});Transcript::new(backend)
}
fn check_state(t:&Transcript,blocks:usize) {
    let mut expected=[0;32];expected[..8].copy_from_slice(&(blocks as u64).to_le_bytes());
    assert_eq!(t.diagnostic_state(),expected);
    SCRIPT.with(|s|{let want:Vec<_>=(0..blocks).flat_map(|i|[(1,i),(2,i)]).collect();assert_eq!(s.borrow().calls,want);});
}
fn main(){
    let mut extra_detection=0;
    for hit in 22..=64 {
        let mut words=vec![0;72];for i in 0..21{words[i]=i as u32;}
        words[hit-1]=21;
        for (i,w) in words.iter_mut().enumerate(){*w|=((i as u32+1)&0x3fff)<<18;}
        let mut t=setup(words);
        assert_eq!(t.challenge_queries_without_replacement(22,1<<18,64).unwrap(),(0..22).collect::<Vec<_>>());
        let blocks=if hit<64{hit/8+1}else{8};check_state(&t,blocks);
        if hit<64 && hit%8==0{assert_eq!(blocks,(hit+7)/8+1);extra_detection+=1;}
        // The *next* squeezed block must start after the detection block too.
        t.squeeze_block();check_state(&t,blocks+1);
    }
    for distinct in 1..22 {
        let words=(0..72).map(|i|(i%distinct)as u32).collect();let mut t=setup(words);
        assert_eq!(t.challenge_queries_without_replacement(22,1<<18,64),Err(QuerySampleError::DrawLimitExhausted{accepted:distinct,max_draws:64}));check_state(&t,8);
    }
    let mut t=setup(vec![0;72]);assert_eq!(t.challenge_queries_without_replacement(22,1<<18,0),Err(QuerySampleError::DrawLimitExhausted{accepted:0,max_draws:0}));check_state(&t,0);
    assert_eq!(t.challenge_queries_without_replacement(0,1<<18,64),Ok(vec![]));check_state(&t,0);
    assert_eq!(t.challenge_queries_without_replacement(22,0,64),Err(QuerySampleError::BoundNotPowerOfTwo{bound:0}));check_state(&t,0);
    assert_eq!(t.challenge_queries_without_replacement(22,3,64),Err(QuerySampleError::BoundNotPowerOfTwo{bound:3}));check_state(&t,0);
    assert_eq!(t.challenge_queries_without_replacement(22,16,64),Err(QuerySampleError::CountExceedsBound{count:22,bound:16}));check_state(&t,0);
    assert_eq!(extra_detection,5);
    println!("R42_QUERY_CONTROL first_hit_cases=43 failure_cases=21 early_return_cases=5 extra_detection_blocks=5 next_block_checks=43 exact_source=true scripted_hash=true sampler_law=false full_privacy=false");
}
