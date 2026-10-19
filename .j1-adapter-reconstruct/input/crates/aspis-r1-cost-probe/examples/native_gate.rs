//! UNPROVED COST PROBE. Honest fixtures, dense comparison and rejection corpus.
use aspis_r1_cost_probe::{prover,dense,trace,transport::Variant,verifier::{self,View,HEADER,INITIAL_QUERY_BYTES},r1_wire};
use aspis_prover::HOST_HASH;
use serde_json::json;
use sha2::{Digest,Sha256};
#[cfg(not(feature="private-leaf-salts"))]
const FIXTURE_ENTROPY_LABEL: &str = "deterministic fixture-only K tail samples via rejection sampling";
#[cfg(feature="private-leaf-salts")]
const FIXTURE_ENTROPY_LABEL: &str = "deterministic fixture-only full-mask entropy and private leaf-salt seed; insecure fixture entropy";
use std::{path::Path,fs};
fn sha(b:&[u8])->String {format!("{:x}",Sha256::digest(b))}
fn write(p:&Path,j:serde_json::Value){assert!(!p.exists());fs::write(p,serde_json::to_string_pretty(&j).unwrap()+"\n").unwrap();}
fn main(){
    assert!(!cfg!(debug_assertions));let args:Vec<_>=std::env::args().collect();
    assert!(args.len()==3||args.len()==4,"usage: native_gate <S1|S2|D> <fresh-output-dir> [fixture-input-dir]");
    let v=match args[1].as_str(){"S1"=>Variant::S1,"S2"=>Variant::S2,"D"=>Variant::D,_=>panic!("variant")};
    let out=Path::new(&args[2]);assert!(!out.join("native-gate.json").exists());fs::create_dir_all(out.join("fixtures")).unwrap();
    let fixture_source=args.get(3).map(|p|Path::new(p));
    if let Some(source)=fixture_source {
        assert_ne!(fs::canonicalize(source).unwrap(),fs::canonicalize(out.join("fixtures")).unwrap(),"reused fixtures must not be written in place");
    }
    let mut records=vec![];
    for (withdrawal,name) in [(false,"transfer"),(true,"withdrawal")] {
        let fixture=aspis_prover::r0_fixture::prepare(withdrawal);
        let public=aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1(&fixture.statement).unwrap();
        let (proof,fixture_public,prover_seconds)=if let Some(source)=fixture_source {
            let proof=fs::read(source.join(format!("{name}.proof.bin"))).unwrap();
            let fixture_public=fs::read(source.join(format!("{name}.public.bin"))).unwrap();
            assert_eq!(fixture_public,public,"reused fixture public bytes differ from freshly encoded deterministic public");
            (proof,fixture_public,0.0)
        } else {
            let seed=HOST_HASH(&[b"UNPROVED:P2:deterministic-fixture",&public]);
            let start=std::time::Instant::now();let proof=prover::prove(fixture.public(),&fixture.compiled,v,HOST_HASH,&seed).unwrap();
            (proof,public.to_vec(),start.elapsed().as_secs_f64())
        };
        let public=fixture_public;
        assert!(!out.join("fixtures").join(format!("{name}.proof.bin")).exists());
        assert!(!out.join("fixtures").join(format!("{name}.public.bin")).exists());
        fs::write(out.join("fixtures").join(format!("{name}.proof.bin")),&proof).unwrap();
        fs::write(out.join("fixtures").join(format!("{name}.public.bin")),&public).unwrap();
        #[cfg(not(feature="private-leaf-salts"))]
        if v==Variant::S2&&fixture_source.is_none() {
            let prior=fs::read(out.parent().unwrap().join("S1/fixtures").join(format!("{name}.proof.bin"))).unwrap();
            assert_eq!(&proof[HEADER..HEADER+verifier::SEMANTIC_BYTES],&prior[HEADER..HEADER+verifier::SEMANTIC_BYTES],"shared semantic bytes changed");
        }
        trace::take();let checkpoint=verifier::tx1(fixture.public(),&public,&proof,11,HOST_HASH,None);
        let actual=checkpoint.as_ref().map_err(|e|*e).and_then(|c|verifier::tx2(&public,&proof,c,HOST_HASH,None));let mut actual_trace=trace::take();
        let expected=dense::verify(fixture.public(),&proof,HOST_HASH);let mut expected_trace=trace::take();
        actual_trace.sort_by_key(|(t,i,_)|(*t,*i));expected_trace.sort_by_key(|(t,i,_)|(*t,*i));
        if actual!=expected||actual_trace!=expected_trace {
            let mismatch=actual_trace.iter().zip(&expected_trace).position(|(a,b)|a!=b);
            write(&out.join("STOP-dense-disagreement.json"),json!({"label":"UNPROVED COST PROBE","fixture":name,"probe":format!("{actual:?}"),"dense":format!("{expected:?}"),"probe_trace_count":actual_trace.len(),"dense_trace_count":expected_trace.len(),"first_mismatch":mismatch,"probe_at_mismatch":mismatch.and_then(|i|actual_trace.get(i)),"dense_at_mismatch":mismatch.and_then(|i|expected_trace.get(i))}));
            panic!("STOP: dense oracle and probe disagree");
        }
        actual.expect("honest acceptance");let checkpoint=checkpoint.unwrap();
        let (p,a)=verifier::resume(&checkpoint,&proof,&public,v,HOST_HASH).unwrap();
        assert_eq!(checkpoint,verifier::checkpoint(&p,&a,&proof,&public,HOST_HASH));
        let trace_bytes:Vec<_>=actual_trace.iter().flat_map(|(t,i,b)|t.to_le_bytes().into_iter().chain((*i as u32).to_le_bytes()).chain(*b)).collect();
        let mut cases=vec![];let mut offsets=vec![];
        for i in [0usize,8,9,15]{offsets.push((format!("header-{i}"),i));}
        let mut offset=HEADER+32;
        for row in 0..27u8 {
            offsets.push((format!("semantic-row-{row}-tag"),offset));
            let size=r1_wire::row_shape(row).unwrap().1;
            if row>=14 {for i in 0..size/32 {offsets.push((format!("semantic-row-{row}-value-{i}"),offset+5+i*32));}}
            offset+=5+size;
        }
        for i in 0..29 {offsets.push((format!("y1-{i}"),offset+i*32));}offset+=29*32;
        offsets.push(("inactive".into(),offset));offset+=32;
        for i in 0..7 {offsets.push((format!("relation0-{i}"),offset+i*32));}offset+=224;
        if v.folds()==2 {offsets.push(("folded-root".into(),offset));offset+=32;for i in 0..7 {offsets.push((format!("relation1-{i}"),offset+i*32));}offset+=224;}
        for i in 0..v.final_len() {offsets.push((format!("final-{i}"),offset+i*32));}offset+=v.final_len()*32;
        let width=(proof.len()-offset)/22;
        for i in 0..22 {
            for (label,j) in [("c1-base",0),("c1-k",104),("c2-k",480)]{offsets.push((format!("query-{i}-{label}"),offset+i*width+j));}
            #[cfg(not(feature="private-leaf-salts"))]
            for (label,j) in [("c1-path",608),("c2-path",608+1344)]{offsets.push((format!("query-{i}-{label}"),offset+i*width+j));}
            #[cfg(feature="private-leaf-salts")]
            for (label,j) in [("c1-salt",608),("c2-salt",640),("c1-path",672),("c2-path",672+1344)]{offsets.push((format!("query-{i}-{label}"),offset+i*width+j));}
            if v.folds()==2 {
                #[cfg(not(feature="private-leaf-salts"))]
                for (label,j) in [("folded-value",INITIAL_QUERY_BYTES),("folded-path",INITIAL_QUERY_BYTES+128)]{offsets.push((format!("query-{i}-{label}"),offset+i*width+j));}
                #[cfg(feature="private-leaf-salts")]
                for (label,j) in [("folded-value",INITIAL_QUERY_BYTES),("folded-salt",INITIAL_QUERY_BYTES+128),("folded-path",INITIAL_QUERY_BYTES+160)]{offsets.push((format!("query-{i}-{label}"),offset+i*width+j));}
            }
        }
        for (label,offset) in offsets {
            let mut bad=proof.clone();bad[offset]^=1;
            let result=verifier::tx1(fixture.public(),&public,&bad,11,HOST_HASH,None).and_then(|c|verifier::tx2(&public,&bad,&c,HOST_HASH,None));
            trace::take();assert!(result.is_err(),"accepted mutation {label}");cases.push(json!({"case":label,"offset":offset,"error":format!("{:?}",result.unwrap_err())}));
        }
        for offset in (0..checkpoint.len()).step_by(16) {
            let mut bad=checkpoint.clone();bad[offset]^=1;let result=verifier::tx2(&public,&proof,&bad,HOST_HASH,None);trace::take();assert!(result.is_err());cases.push(json!({"case":"checkpoint-byte","offset":offset,"error":format!("{:?}",result.unwrap_err())}));
        }
        let mut wrong_public=public.clone();wrong_public[0]^=1;assert!(verifier::tx2(&wrong_public,&proof,&checkpoint,HOST_HASH,None).is_err());
        cases.push(json!({"case":"checkpoint-public-binding","error":"rejected"}));
        assert!(cases.len()>=200);
        #[cfg(feature="private-leaf-salts")]
        {
            let mut old_magic=proof.clone();old_magic[..8].copy_from_slice(b"R1P2COST");
            assert!(verifier::tx1(fixture.public(),&public,&old_magic,11,HOST_HASH,None).is_err());
            cases.push(json!({"case":"P2-magic-rejected","error":"rejected"}));
        }
        write(&out.join(format!("{name}-mutations.json")),json!({"label":"UNPROVED COST PROBE","count":cases.len(),"cases":cases}));
        write(&out.join("fixtures").join(format!("{name}.fixture.json")),json!({"label":"UNPROVED COST PROBE","fixture_mode":if fixture_source.is_some(){"reused"}else{"generated"},"fixture_source_dir":fixture_source.map(|p|p.display().to_string()),"proof_bytes":proof.len(),"proof_sha256":sha(&proof),"public_bytes":public.len(),"public_sha256":sha(&public),"entropy":FIXTURE_ENTROPY_LABEL,"prover_seconds":prover_seconds}));
        records.push(json!({"fixture":name,"native_acceptance":true,"dense_acceptance":true,"all_challenge_weight_check_bytes_equal":true,"trace_count":actual_trace.len(),"trace_bytes":trace_bytes.len(),"trace_sha256":sha(&trace_bytes),"checkpoint_roundtrip":true,"checkpoint_bytes":checkpoint.len(),"proof_bytes":proof.len(),"mutations_rejected":cases.len(),"fixture_mode":if fixture_source.is_some(){"reused"}else{"generated"},"prover_seconds":prover_seconds}));
        std::println!("{}: honest acceptance, dense trace agreement, {} mutations rejected",name,cases.len());
    }
    write(&out.join("native-gate.json"),json!({"label":if cfg!(feature="private-leaf-salts"){"UNPROVED P3 full-mask cost probe"}else{"UNPROVED R1 COST PROBE"},"variant":args[1],"source_revision":std::env::var("ASPIS_SOURCE_REVISION").unwrap(),"fixture_mode":if fixture_source.is_some(){"reused"}else{"generated"},"fixture_source_dir":fixture_source.map(|p|p.display().to_string()),"fixtures":records}));
}
