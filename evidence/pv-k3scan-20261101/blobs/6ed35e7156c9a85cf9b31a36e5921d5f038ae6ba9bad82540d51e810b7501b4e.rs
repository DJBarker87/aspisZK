use sha2::{Digest,Sha256};
use std::{hint::black_box,time::Instant};
#[cfg(feature="count")]
fn count() {
    use std::{collections::BTreeMap,sync::{Mutex,LazyLock}};
    static HIST:LazyLock<Mutex<BTreeMap<String,u64>>>=LazyLock::new(||Mutex::new(BTreeMap::new()));
    fn counted(parts:&[&[u8]])->[u8;32] {
        *HIST.lock().unwrap().entry(parts.iter().map(|x|x.len().to_string()).collect::<Vec<_>>().join("+")).or_default()+=1;
        aspis_prover::HOST_HASH(parts)
    }
    let fixture=aspis_prover::r0_fixture::prepare(false);
    HIST.lock().unwrap().clear();
    let result=aspis_r1_cost_probe::prover::prove_masked_fixture(
        fixture.public(),&fixture.compiled,aspis_r1_cost_probe::transport::Variant::S2,
        counted,&[37u8;32]);
    let hist=HIST.lock().unwrap();
    println!("{}",serde_json::json!({"mode":"count","fixture":"transfer, S2, deterministic seed [37;32]","accepted":result.is_ok(),"proof_bytes":result.as_ref().ok().map(|x|x.0.len()),"sha_callback_calls":hist.values().sum::<u64>(),"parts_length_histogram":*hist,"scope":"passed HashFn callback during one fixture proof; setup and independent direct calls excluded; no timing gate"}));
    assert!(result.is_ok());
}
fn main() {
    assert!(!cfg!(debug_assertions));
    if std::env::args().nth(1).as_deref()==Some("count") {
        #[cfg(feature="count")] {count();return;}
        #[cfg(not(feature="count"))] panic!("build with count feature");
    }
    let sizes=std::env::args().nth(1).unwrap_or("0,32,64,80,128,512,1024,16384".to_string());
    let mut rows=Vec::new();
    for shape in sizes.split(',') {
        let lengths:Vec<usize>=shape.split('+').map(|s|s.parse().unwrap()).collect();
        let n:usize=lengths.iter().sum();
        let data=vec![0x5au8;n];
        let mut at=0;let parts:Vec<&[u8]>=lengths.iter().map(|len|{let part=&data[at..at+len];at+=len;part}).collect();
        let iterations=(32_000_000usize/(n+64)).clamp(4000,300000);
        let mut times=Vec::new();let mut digest=String::new();
        for _ in 0..7 {
            let start=Instant::now();
            for _ in 0..iterations {let mut h=Sha256::new();for part in black_box(&parts){h.update(part);}let out=h.finalize();black_box(out);}
            times.push(start.elapsed().as_nanos() as f64/iterations as f64);
        }
        times.sort_by(|a,b|a.partial_cmp(b).unwrap());
        for x in Sha256::digest(&data) {digest.push_str(&format!("{x:02x}"));}
        rows.push(serde_json::json!({"length":n,"parts":lengths,"shape":shape,"iterations":iterations,"ns_per_call_median":times[3],"ns_per_call_samples":times,"digest":digest}));
    }
    println!("{}",serde_json::json!({"mode":"microbench","force_soft":cfg!(feature="soft"),"sha_detected":std::is_x86_feature_detected!("sha"),"sse2":std::is_x86_feature_detected!("sse2"),"ssse3":std::is_x86_feature_detected!("ssse3"),"sse4.1":std::is_x86_feature_detected!("sse4.1"),"rows":rows}));
}
