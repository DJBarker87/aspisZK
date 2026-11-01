//! Full retry-owner differential: varied honest statements/coins and error tapes.
//! Run separately against the v2 and candidate source, then compare full files.
use aspis_core::{digest::LegacyHashFn,HashFn};
use aspis_prover::{state_only_entropy::{DurableStateOnlyMaskNonceStore,StateOnlyAttemptSecrets},state_only_hiding::StateOnlyMaskNonceStore,HOST_HASH};
use aspis_r1_cost_probe::{prover,transport::Variant,verifier};
use std::{fs,io::{BufWriter,Write},path::Path,sync::{Mutex,atomic::{AtomicUsize,Ordering::SeqCst}}};
use serde_json::json;
#[path="../../../tools/prover-rw-20261023/varied-fixture.rs"] mod varied_fixture;
#[cfg(target_os="linux")]
#[path="../../../tools/prover-rw-20261023/ledger-watch.rs"] mod ledger_watch;
static LOG:Mutex<Option<BufWriter<fs::File>>>=Mutex::new(None);
static MODE:AtomicUsize=AtomicUsize::new(0);
static REJECT_SEED:Mutex<[u8;32]>=Mutex::new([0;32]);
fn oracle(parts:&[&[u8]])->[u8;32] {
    let mode=MODE.load(SeqCst);
    let value=if parts.first()==Some(&b"aspis:state-only:private-mask-expand:v1".as_slice()) {
        if mode==2 || (mode==3 && parts[1]==&*REJECT_SEED.lock().unwrap()) {[255;32]} else {HOST_HASH(parts)}
    } else {HOST_HASH(parts)};
    // Exact ordered oracle inputs and outputs, including rejected suffixes.
    if let Some(log)=LOG.lock().unwrap().as_mut() {
        log.write_all(&(parts.len() as u32).to_le_bytes()).unwrap();
        for part in parts {log.write_all(&(part.len() as u64).to_le_bytes()).unwrap();log.write_all(part).unwrap();}
        log.write_all(&value).unwrap();
    }
    value
}
#[cfg(not(target_os="linux"))]
fn main() {panic!("This diagnostic gate targets x86_64 Linux.");}
#[cfg(target_os="linux")]
fn main() {
    assert!(!cfg!(debug_assertions));
    let args:Vec<_>=std::env::args().collect();
    assert_eq!(args.len(),5,"usage: prover_rw_differential fresh-dir first count oracle-log");
    let out=Path::new(&args[1]);assert!(!out.exists());fs::create_dir_all(out).unwrap();
    let first:u64=args[2].parse().unwrap();let count:u64=args[3].parse().unwrap();
    let log_oracle=args[4]=="1";
    for coin in first..first+count {
        let withdrawal=coin%2==1;
        let fixture=varied_fixture::prepare(withdrawal,coin);
        let public=fixture.public();let public_bytes=public.public_bytes().unwrap();
        let run=out.join(format!("{coin}"));fs::create_dir(&run).unwrap();
        let mut store=DurableStateOnlyMaskNonceStore::open(run.join("ledger")).unwrap();
        let seed=|domain:&[u8],attempt:usize| HOST_HASH(&[b"PROVER-RW:differential",domain,&public_bytes,&coin.to_le_bytes(),&(attempt as u64).to_le_bytes()]);
        let mode=(coin as usize/2)%10;
        // Ten tape classes: entropy failure; repeated reservation; mask decode
        // exhaustion; one rejected attempt then real execution; ledger I/O
        // failure; five ordinary. Both variants enter every tape class.
        if mode==1 {assert!(store.reserve(HOST_HASH(&[&public_bytes]),seed(b"nonce",0)));}
        let mut watcher=ledger_watch::LedgerWatch::new(&run.join("ledger"));
        let mut l1_events=Vec::new();
        if mode==4 {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(run.join("ledger"),fs::Permissions::from_mode(0o500)).unwrap();
        }
        let context=aspis_core::state_only_hiding::StateOnlyHidingContext::pool_v1_pair_forest_v1(HOST_HASH(&[&public_bytes]),seed(b"nonce",0));
        let binding=HOST_HASH(&[b"UNPROVED:R1:P3:PRIVATE-ATTEMPT",&public_bytes,&[Variant::S2.tag()],&context.encode()]);
        *REJECT_SEED.lock().unwrap()=HOST_HASH(&[b"aspis:state-only:private-mask-seed:v1",&binding,&context.encode(),&seed(b"field",0)]);
        MODE.store(mode,SeqCst);
        if log_oracle {*LOG.lock().unwrap()=Some(BufWriter::new(fs::File::create(run.join("oracle.bin")).unwrap()));}
        let mut callbacks=Vec::new();
        let result=prover::prove_masked_retrying_with(public,&fixture.compiled,Variant::S2,oracle as HashFn,&mut store,|k| {
            for event in watcher.drain() {l1_events.push(json!(["ledger",event.0,event.1]));}
            l1_events.push(json!(["entropy_callback",k]));
            callbacks.push(k);
            if mode==0 {return Err(verifier::Error::Entropy);}
            Ok(StateOnlyAttemptSecrets::deterministic_spend_fixture(seed(b"nonce",k),seed(b"field",k),seed(b"leaf",k)))
        });
        for event in watcher.drain() {l1_events.push(json!(["ledger",event.0,event.1]));}
        if let Some(mut log)=LOG.lock().unwrap().take() {log.flush().unwrap();}
        #[cfg(feature="public-work-trace")] let work=aspis_r1_cost_probe::host_work::take_trace();
        #[cfg(not(feature="public-work-trace"))] let work:Vec<[usize;6]>=Vec::new();
        let mut records:Vec<_>=fs::read_dir(run.join("ledger")).unwrap().map(|p|{let p=p.unwrap().path();(p.file_name().unwrap().to_string_lossy().into_owned(),fs::read(p).unwrap())}).collect();records.sort();
        let mut row=json!({"ledger_io_error":format!("{:?}",store.last_error()),"coin":coin,"withdrawal":withdrawal,"mode":mode,"callbacks":callbacks,"ledger_records":records,"l1_events":l1_events,"public_work":work});
        match result {
            Ok(r)=>{
                assert!(mode==3 || mode>=5);
                if mode==3 {assert!(r.attempts>=2);}
                row["status"]=json!("Ok");row["attempts"]=json!(r.attempts);row["audit"]=json!(format!("{:?}",r.audit));
                // The published attempt uses the ordinary hash after the forced
                // rejected prefix, so strict verification uses the real hash.
                let cp=verifier::tx1(public,&public_bytes,&r.proof,verifier::SPLIT,LegacyHashFn(HOST_HASH),None).unwrap();
                verifier::tx2(&public_bytes,&r.proof,&cp,LegacyHashFn(HOST_HASH),None).unwrap();
                fs::write(run.join("proof.bin"),&r.proof).unwrap();
                row["published_bytes"]=json!(r.proof.len());
            }
            Err(e)=>{
                assert!(matches!(mode,0|1|2|4),"unexpected error on a successful tape class: {e:?}");
                row["status"]=json!(format!("{e:?}"));row["published_bytes"]=json!(0);
                if mode==0 {assert_eq!(e,verifier::Error::Entropy);}
                if mode==1 {assert_eq!(e,verifier::Error::Semantic);}
                if mode==2 {assert_eq!(e,verifier::Error::AttemptsExhausted);assert_eq!(callbacks.len(),prover::ATTEMPT_CAP);}
                if mode==4 {assert_eq!(e,verifier::Error::Semantic);assert_eq!(store.last_error(),Some(std::io::ErrorKind::PermissionDenied));}
            }
        }
        let returned=json!(["return",row["status"].clone(),row["published_bytes"].clone()]);
        row["l1_events"].as_array_mut().unwrap().push(returned);
        fs::write(run.join("public.bin"),public_bytes).unwrap();
        fs::write(run.join("result.json"),serde_json::to_vec_pretty(&row).unwrap()).unwrap();
        println!("PROVER_RW case={coin} mode={mode} status={}",row["status"]);
    }
}
