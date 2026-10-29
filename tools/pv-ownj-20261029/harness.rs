use aspis_core::field::{CM31,M31,QM31,WideExact};
use aspis_core::state_only_prefix::r0 as wire;
use aspis_prover::state_only_candidate_prefix::r0::point_claims;
use aspis_prover::state_only_hiding::r0::prove_sumcheck;
fn q(n:u32)->QM31 { QM31::from_cm31(CM31::from_m31(M31(n))) }
// Fixed deterministic hash for data-flow validation, not a cryptographic claim.
fn hash(parts:&[&[u8]])->[u8;32] {
    let mut x=0xcbf29ce484222325u64;
    for p in parts {for &b in *p {x^=u64::from(b);x=x.wrapping_mul(0x100000001b3);}}
    let mut out=[0;32];
    for chunk in out.chunks_exact_mut(8) {x^=x>>12;x^=x<<25;x^=x>>27;chunk.copy_from_slice(&x.wrapping_mul(2685821657736338717).to_le_bytes());}
    out
}
fn dense(column:&[QM31],point:&[QM31;10])->QM31 {
    let mut sum=QM31::ZERO;
    for (row,value) in column.iter().enumerate() {
        let mut w=QM31::ONE;
        for i in 0..10 {w=w.mul(if row>>(9-i)&1==0 {QM31::ONE.sub(point[i])}else{point[i]});}
        sum=sum.add(w.mul(*value));
    } sum
}
fn main() {
    let columns:[Vec<QM31>;29]=std::array::from_fn(|lane|(0..1024).map(|row|q(((lane*71+row*13+row*row)%997)as u32)).collect());
    let point=std::array::from_fn(|i|if i>=7 {q((i%2)as u32)}else{q((i+2)as u32)});
    let got=point_claims(&columns,&point).unwrap();
    for (i,p) in wire::statement_points(&point).iter().enumerate() {for lane in 0..29 {assert_eq!(got[i][lane],dense(&columns[lane],p));}}
    let boolean=[QM31::ZERO;10];
    for bad in 0..29 {let mut malformed=columns.clone();malformed[bad].pop();assert_eq!(point_claims(&malformed,&boolean),Err(wire::Error::Public));}
    let public=b"public statement fixture";let c1=[19;32];
    let mut total_queries=0;
    for constant in [0,1] {
        let mut transcript=wire::SemanticTranscript::new(hash,public,&c1).unwrap();
        let mut published=Vec::new();
        let mut initial_frames=Vec::new();
        for row in 0..15 {
            let payload=if row==2 {vec![23;32]}else if row==14 {WideExact::from_qm31(q(1024*constant)).to_le_bytes().to_vec()}else{vec![]};
            let frame=wire::record(row,&payload).unwrap();transcript.semantic(row,&frame).unwrap();initial_frames.push(frame);
        }
        let mut queries=Vec::new();
        let (alpha,_)=prove_sumcheck(&mut transcript,&mut published,q(1024*constant),|p|{queries.push(*p);Ok(q(constant))}).unwrap();
        let mut replay=wire::SemanticTranscript::new(hash,public,&c1).unwrap();
        for (row,frame) in initial_frames.iter().enumerate() {replay.semantic(row as u8,frame).unwrap();}
        let mut reconstructed=[QM31::ZERO;10];let frame_size=5+28*32;
        assert_eq!(published.len(),10*frame_size);
        for round in 0..10 {reconstructed[round]=replay.semantic(15+round as u8,&published[round*frame_size..(round+1)*frame_size]).unwrap();}
        assert_eq!(alpha,reconstructed);
        let mut n=0;
        for round in 0..10 {for sample in 0..28 {for assignment in 0..1usize<<(9-round) {
            let mut expected=[QM31::ZERO;10];expected[..round].copy_from_slice(&reconstructed[..round]);expected[round]=q(sample);
            for offset in 0..9-round {expected[round+1+offset]=q(((assignment>>(9-round-1-offset))&1)as u32);}
            assert_eq!(queries[n],expected);n+=1;
        }}}
        assert_eq!(queries[n],alpha);assert_eq!(queries.len(),n+1);total_queries+=queries.len();
        // Independent literal source hash-state replay, excluding private oracle values.
        let mut state=hash(&[wire::DOMAIN,&[0],&(public.len()as u32).to_le_bytes(),public,&c1]);
        for (row,frame) in initial_frames.iter().map(|x|x.as_slice()).chain(published.chunks_exact(frame_size)).enumerate() {
            let absorbed=hash(&[&state,&[0,0xa0+row as u8],frame]);
            if row>=15 {assert_eq!(reconstructed[row-15],aspis_core::r0_transcript::qm31_sample(&hash(&[&absorbed,&[1]])));}
            state=hash(&[&absorbed,&[2]]);
        }
        assert_eq!(state,transcript.state());assert_eq!(replay.state(),transcript.state());
    }
    println!("consuming dense comparisons=87; malformed lanes=29; published-data query reconstructions={total_queries}; final-alpha reconstructions=2");
}
