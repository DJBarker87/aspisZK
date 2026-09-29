//! Actual wrapper APIs versus complete executable Lean traces. Scripted oracle,
//! not a source probability theorem or circle inversion refinement.
use aspis_core::transcript::{Transcript,OodSampleError};
use aspis_core::field::QM31;
use std::{cell::RefCell,collections::BTreeMap,io::{BufRead,BufReader}};
#[derive(Default)]
struct Script {raw:Vec<u32>,frozen:bool,trace:Vec<u8>,table:BTreeMap<Vec<u8>,[u8;32]>}
thread_local!{static SCRIPT:RefCell<Script>=RefCell::new(Script::default());}
fn oracle(parts:&[&[u8]])->[u8;32]{
    let input:Vec<u8>=parts.iter().flat_map(|p|p.iter().copied()).collect();
    assert_eq!(input.len(),33);assert!(input[4..32].iter().all(|&b|b==0));
    let counter=u32::from_le_bytes(input[..4].try_into().unwrap())as usize;
    SCRIPT.with(|s|{let mut s=s.borrow_mut();let mut answer=[0;32];
        match input[32]{
            1=>for j in 0..8{answer[4*j..4*j+4].copy_from_slice(&s.raw[counter*8+j].to_le_bytes());},
            2=>answer[..4].copy_from_slice(&((counter+usize::from(!s.frozen))as u32).to_le_bytes()),
            _=>panic!("unexpected hash domain"),
        }
        if let Some(old)=s.table.insert(input.clone(),answer){assert_eq!(old,answer);}
        s.trace.extend(&input);s.trace.extend(answer);answer
    })
}
fn numbers(s:&str)->Vec<u32>{if s.is_empty(){vec![]}else{s.split(',').map(|x|x.parse().unwrap()).collect()}}
fn field(x:QM31)->String{format!("ok:{},{},{},{}",x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0)}
fn main(){
    let path=std::env::args().nth(1).expect("Lean fixture path");
    let reader=BufReader::new(std::fs::File::open(path).unwrap());
    let(mut total,mut nonzero,mut ood,mut calls,mut hits)=(0,0,0,0,0);
    for(case,line)in reader.lines().enumerate(){let line=line.unwrap();let parts:Vec<_>=line.split('|').collect();assert_eq!(parts.len(),6);
        let raw=numbers(parts[2]);assert_eq!(raw.len(),128);
        SCRIPT.with(|s|*s.borrow_mut()=Script{raw,frozen:parts[1]=="1",..Script::default()});
        let mut t=Transcript::new(oracle);
        let answer=match parts[0]{
            "n"=>{nonzero+=1;match t.challenge_nonzero_qm31(){Ok(x)=>field(x),Err(_)=>"err:challenge".into()}},
            "o"=>{ood+=1;match t.challenge_ood_qm31(){Ok(x)=>field(x),
                Err(OodSampleError::ChallengeSampleExhausted)=>"err:challenge".into(),
                Err(OodSampleError::SubfieldSampleExhausted)=>"err:subfield".into()}},
            _=>panic!("unexpected wrapper kind"),
        };
        assert_eq!(answer,parts[3],"case {case} outcome");
        assert_eq!(t.diagnostic_state().map(u32::from).to_vec(),numbers(parts[4]),"case {case} final state");
        SCRIPT.with(|s|{let s=s.borrow();
            assert_eq!(s.trace.iter().copied().map(u32::from).collect::<Vec<_>>(),numbers(parts[5]),"case {case} complete trace");
            assert_eq!(s.trace.len()%65,0);let n=s.trace.len()/65;calls+=n;hits+=n-s.table.len();
        });total+=1;
    }
    assert_eq!((total,nonzero,ood),(358,179,179));assert!(hits>0);
    println!("R54_SOURCE_REPLAY cases={total} nonzero_cases={nonzero} ood_cases={ood} hash_calls={calls} cache_hits={hits} complete_trace_bytes_equal=true final_states_equal=true results_errors_equal=true scripted_oracle=true circle_word_refinement=false universal_Rust_refinement=false source_probability=false full_privacy=false");
}
