//! Cost-only G_R1 corpus, built against the frozen v3b source archive.
//! The public random seed is test input, not production entropy.
use aspis_prover::HOST_HASH;
use aspis_r1_cost_probe::{dense, prover, r1_wire, trace, transport::Variant, verifier::{self, HEADER, SEMANTIC_BYTES, INITIAL_QUERY_BYTES, SECOND_QUERY_BYTES}};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::{fs, path::Path};
fn sha(b: &[u8]) -> String { format!("{:x}", Sha256::digest(b)) }
fn write(p: &Path, v: Value) { assert!(!p.exists()); fs::write(p, serde_json::to_string_pretty(&v).unwrap()+"\n").unwrap(); }
fn audit_case(label: String, region: &str, public: &[u8], proof: &[u8], checkpoint: &[u8], cases: &mut Vec<Value>) {
    trace::take();
    let strict=verifier::tx2(public,proof,checkpoint,HOST_HASH,None);
    let st=trace::take();
    let authenticated=verifier::tx2_authenticated(public,proof,checkpoint,HOST_HASH,None);
    let at=trace::take();
    assert!(strict.is_err() && authenticated.is_err(), "accepted {label}: {strict:?}/{authenticated:?}");
    assert!(st.is_empty() && at.is_empty(), "arithmetic before rejection: {label}");
    cases.push(json!({"case":label,"region":region,"strict":format!("{strict:?}"),"authenticated":format!("{authenticated:?}"),"strict_trace_entries":st.len(),"authenticated_trace_entries":at.len(),"proof_sha256":sha(proof),"public_sha256":sha(public),"checkpoint_sha256":sha(checkpoint)}));
}
fn main() {
    assert!(!cfg!(debug_assertions));
    let args:Vec<_>=std::env::args().collect(); assert_eq!(args.len(),3,"gr1_native_gate <fresh-output> <64-hex seed>");
    let seed:[u8;32]=core::array::from_fn(|i|u8::from_str_radix(&args[2][2*i..2*i+2],16).unwrap());
    let out=Path::new(&args[1]); assert!(!out.exists()); fs::create_dir_all(out.join("fixtures")).unwrap();
    let mut records=vec![];
    for (withdrawal,name) in [(false,"transfer"),(true,"withdrawal")] {
        let f=aspis_prover::r0_fixture::prepare(withdrawal);
        let public=aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1(&f.statement).unwrap();
        let (proof,audit)=prover::prove_masked_fixture(f.public(),&f.compiled,Variant::S2,HOST_HASH,&seed).unwrap();
        trace::take(); let cp=verifier::tx1(f.public(),&public,&proof,10,HOST_HASH,None).unwrap(); let t1=trace::take();
        verifier::tx2(&public,&proof,&cp,HOST_HASH,None).unwrap(); let mut strict=trace::take();
        verifier::tx2_authenticated(&public,&proof,&cp,HOST_HASH,None).unwrap(); let mut auth=trace::take();
        strict.sort();auth.sort();assert_eq!(strict,auth);
        let mut combined=t1.clone(); combined.extend(strict.clone());combined.sort();
        dense::verify(f.public(),&proof,HOST_HASH).unwrap();let mut reference=trace::take();reference.sort();assert_eq!(combined,reference);
        let trace_bytes:Vec<_>=combined.iter().flat_map(|(t,i,b)|t.to_le_bytes().into_iter().chain((*i as u32).to_le_bytes()).chain(*b)).collect();
        let mut cases=vec![];
        let mut bad_field=|label:String,region:&str,offset:usize,high:bool| {
            let mut bad=proof.clone();bad[offset..offset+4].copy_from_slice(&(if high {1u32}else{u32::MAX}).to_le_bytes());
            assert_ne!(bad,proof);
            let tx1=verifier::tx1(f.public(),&public,&bad,10,HOST_HASH,None);trace::take();assert!(tx1.is_err(),"tx1 accepted {label}");
            audit_case(label,region,&public,&bad,&cp,&mut cases);
            cases.last_mut().unwrap()["tx1"]=json!(format!("{:?}",tx1.unwrap_err()));
        };
        let mut at=HEADER+32;let mut rows=vec![];
        for row in 0..27u8 {
            let size=r1_wire::row_shape(row).unwrap().1; rows.push((at,5+size));
            if row>=14 {for i in 0..size/32 {
                bad_field(format!("row-{row}-value-{i}-noncanonical"),"semantic canonicality",at+5+32*i,false);
                bad_field(format!("row-{row}-value-{i}-high-component"),"semantic subfield",at+5+32*i+16,true);
            }} at+=5+size;
        }
        let y=HEADER+SEMANTIC_BYTES;
        for i in 0..29 {bad_field(format!("y1-{i}-canonical"),"y1",y+32*i,false);bad_field(format!("y1-{i}-subfield"),"y1",y+32*i+16,true);}
        let inactive=y+29*32; bad_field("inactive-canonical".into(),"retained inactive",inactive,false);
        let r0=inactive+32;let r1=r0+224+32;let fin=r1+224;
        for (label,start,n) in [("round0",r0,7),("round1",r1,7),("final",fin,64)] {for i in 0..n {for limb in 0..8 {bad_field(format!("{label}-{i}-limb-{limb}"),label,start+i*32+limb*4,false);}}}
        let q0=fin+64*32;let width=INITIAL_QUERY_BYTES+SECOND_QUERY_BYTES;
        for q in 0..22 {for slot in 0..4 {
            for lane in 0..26 {bad_field(format!("query-{q}-slot-{slot}-M31-{lane}"),"query base",q0+q*width+slot*120+lane*4,false);}
            for limb in 0..4 {bad_field(format!("query-{q}-slot-{slot}-D-{limb}"),"query D",q0+q*width+slot*120+104+limb*4,false);}
            for limb in 0..8 {bad_field(format!("query-{q}-slot-{slot}-HG-{limb}"),"query H1/G",q0+q*width+480+slot*32+limb*4,false);bad_field(format!("query-{q}-slot-{slot}-folded-{limb}"),"query folded",q0+q*width+INITIAL_QUERY_BYTES+slot*32+limb*4,false);}
        }}
        drop(bad_field);
        for (row,(offset,_)) in rows.iter().enumerate() {for (label,delta) in [("tag",0),("length",1)] {
            let mut bad=proof.clone();bad[offset+delta]^=1;
            let tx1=verifier::tx1(f.public(),&public,&bad,10,HOST_HASH,None);trace::take();assert!(tx1.is_err());
            audit_case(format!("row-{row}-{label}"),"framing",&public,&bad,&cp,&mut cases);cases.last_mut().unwrap()["tx1"]=json!(format!("{:?}",tx1.unwrap_err()));
        }}
        // Same-size nonempty round records have no explicit row-id: order is positional/transcript bound.
        for row in 15..24 {let (a,n)=rows[row];let (b,m)=rows[row+1];assert_eq!(n,m);let mut bad=proof.clone();bad[a..a+n].copy_from_slice(&proof[b..b+n]);bad[b..b+n].copy_from_slice(&proof[a..a+n]);assert_ne!(bad,proof);
            let tx1=verifier::tx1(f.public(),&public,&bad,10,HOST_HASH,None);trace::take();assert!(tx1.is_err());
            audit_case(format!("swap-rows-{row}-{}",row+1),"row order",&public,&bad,&cp,&mut cases);cases.last_mut().unwrap()["tx1"]=json!(format!("{:?}",tx1.unwrap_err()));
        }
        for offset in [0usize,8,9,15] {let mut bad=proof.clone();bad[offset]^=1;audit_case(format!("proof-header-{offset}"),"retained header",&public,&bad,&cp,&mut cases);}
        let mut bad=proof.clone();bad.push(0);audit_case("proof-trailing-byte".into(),"retained exact length",&public,&bad,&cp,&mut cases);
        audit_case("proof-truncated".into(),"retained exact length",&public,&proof[..proof.len()-1],&cp,&mut cases);
        for offset in 0..16 {let mut bad=cp.clone();bad[offset]=if offset==9 {23}else{bad[offset]^1};let end=bad.len()-32;let digest=HOST_HASH(&[b"UNPROVED:R1:checkpoint",&bad[..end]]);bad[end..].copy_from_slice(&digest);audit_case(format!("checkpoint-header-{offset}-rechecksummed"),"retained checkpoint header",&public,&proof,&bad,&mut cases);}
        let mut bad=cp.clone();bad.push(0);audit_case("checkpoint-trailing".into(),"retained checkpoint length",&public,&proof,&bad,&mut cases);
        audit_case("checkpoint-truncated".into(),"retained checkpoint length",&public,&proof,&cp[..cp.len()-1],&mut cases);
        for offset in [16,48,80,cp.len()-1] {let mut bad=cp.clone();bad[offset]^=1;audit_case(format!("checkpoint-binding-{offset}"),"checkpoint digest",&public,&proof,&bad,&mut cases);}
        let mut bad=public.clone();bad[0]^=1;audit_case("public-binding".into(),"public digest",&bad,&proof,&cp,&mut cases);
        let meta=json!({"label":"G_R1 cost-only complete random mask tape","seed_hex":args[2],"seed_source":"OS random 32 bytes recorded before proving; SHA-256 deterministic expansion for reproducibility","fixture":name,"proof_sha256":sha(&proof),"proof_bytes":proof.len(),"public_sha256":sha(&public),"public_bytes":public.len(),"mask_audit":format!("{audit:?}"),"native_dense_equal":true,"strict_authenticated_equal":true,"trace_count":combined.len(),"tx2_trace_count":strict.len(),"trace_sha256":sha(&trace_bytes),"mutation_count":cases.len()});
        fs::write(out.join("fixtures").join(format!("{name}.proof.bin")),&proof).unwrap();fs::write(out.join("fixtures").join(format!("{name}.public.bin")),&public).unwrap();
        write(&out.join("fixtures").join(format!("{name}.fixture.json")),meta.clone());write(&out.join(format!("{name}-mutations.json")),json!({"cases":cases}));records.push(meta);
        println!("{name}: native/dense/strict/authenticated equality; {} mutations rejected",cases.len());
    }
    write(&out.join("native-gate.json"),json!({"seed_hex":args[2],"fixtures":records,"source_revision":std::env::var("ASPIS_SOURCE_REVISION").unwrap()}));
}
