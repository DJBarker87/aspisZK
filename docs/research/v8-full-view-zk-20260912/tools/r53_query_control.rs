//! Differential replay of executable Lean sampler programs against actual Rust.
//! Scripted functional oracle; compare EVERY call's address and answer bytes.
use aspis_core::transcript::{Transcript, QuerySampleError, ChallengeSampleExhausted};
use aspis_core::field::QM31;
use std::{cell::RefCell,collections::BTreeMap,io::{BufRead,BufReader}};

#[derive(Default)]
struct Script { raw:Vec<u32>, frozen:bool, trace:Vec<u8>, table:BTreeMap<Vec<u8>,[u8;32]> }
thread_local! {static SCRIPT:RefCell<Script>=RefCell::new(Script::default());}
fn oracle(parts:&[&[u8]])->[u8;32] {
    let input:Vec<u8>=parts.iter().flat_map(|p|p.iter().copied()).collect();
    assert_eq!(input.len(),33);assert!(input[4..32].iter().all(|&b|b==0));
    let counter=u32::from_le_bytes(input[..4].try_into().unwrap())as usize;
    SCRIPT.with(|s|{let mut s=s.borrow_mut();let mut answer=[0;32];
        match input[32] {
            1=>for j in 0..8{answer[4*j..4*j+4].copy_from_slice(&s.raw[counter*8+j].to_le_bytes());},
            2=>answer[..4].copy_from_slice(&((counter+usize::from(!s.frozen))as u32).to_le_bytes()),
            _=>panic!("unexpected source hash domain"),
        }
        if let Some(old)=s.table.insert(input.clone(),answer){assert_eq!(old,answer);}
        s.trace.extend(&input);s.trace.extend(answer);answer
    })
}
fn numbers(s:&str)->Vec<u32>{if s.is_empty(){vec![]}else{s.split(',').map(|x|x.parse().unwrap()).collect()}}
fn field(r:Result<QM31,ChallengeSampleExhausted>)->String {
    match r {Ok(x)=>format!("ok:{},{},{},{}",x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0),Err(_)=>"err".into()}
}
fn main(){
    let path=std::env::args().nth(1).expect("Lean-generated fixture file");
    let reader=BufReader::new(std::fs::File::open(path).unwrap());
    let(mut total,mut fields,mut queries,mut double,mut calls,mut hits)=(0,0,0,0,0,0);
    for (case,line)in reader.lines().enumerate(){let line=line.unwrap();let parts:Vec<_>=line.split('|').collect();assert_eq!(parts.len(),6);
        let raw=numbers(parts[2]);assert_eq!(raw.len(),72);
        SCRIPT.with(|s|*s.borrow_mut()=Script{raw,frozen:parts[1]=="1",..Script::default()});
        let mut t=Transcript::new(oracle);
        let answer=match parts[0]{
            "f"=>{fields+=1;field(t.challenge_qm31())},
            "ff"=>{double+=1;format!("{}/{}",field(t.challenge_qm31()),field(t.challenge_qm31()))},
            "q"=>{queries+=1;match t.challenge_queries_without_replacement(22,1<<18,64){
                Ok(v)=>format!("ok:{}",v.iter().map(u32::to_string).collect::<Vec<_>>().join(",")),
                Err(QuerySampleError::DrawLimitExhausted{accepted,max_draws})=>{assert_eq!(max_draws,64);format!("err:{accepted}")},
                Err(e)=>panic!("unexpected early query error {e:?}"),
            }},_=>panic!("unknown fixture kind"),
        };
        assert_eq!(answer,parts[3],"case {case} returned value/error");
        assert_eq!(t.diagnostic_state().map(u32::from).to_vec(),numbers(parts[4]),"case {case} final state");
        SCRIPT.with(|s|{let s=s.borrow();
            assert_eq!(s.trace.iter().copied().map(u32::from).collect::<Vec<_>>(),numbers(parts[5]),"case {case} COMPLETE trace");
            assert_eq!(s.trace.len()%65,0);let n=s.trace.len()/65;calls+=n;hits+=n-s.table.len();
        });total+=1;
    }
    assert_eq!((total,fields,queries,double),(4753,4684,65,4));assert!(hits>0);
    println!("R53_SOURCE_REPLAY cases={total} field_cases={fields} query_cases={queries} sequential_cases={double} hash_calls={calls} cache_hits={hits} complete_trace_bytes_equal=true final_states_equal=true results_errors_equal=true scripted_oracle=true universal_Rust_refinement=false source_probability=false full_privacy=false");
}
